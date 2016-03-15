(*  Title:      Construct_SSA.thy
    Author:     Sebastian Ullrich
*)

section {* SSA Construction *}
subsection {* CFG to SSA CFG *}

theory Construct_SSA imports SSA_CFG
  "~~/src/HOL/Library/While_Combinator"
  "~~/src/HOL/Library/Product_Lexorder"
begin

type_synonym ('node, 'var) ssaVal = "'var \<times> 'node"

locale CFG_Construct = CFG \<alpha>n predecessors Entry "defs" "uses"
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  "defs" :: "'node \<Rightarrow> 'var::linorder set" and
  "uses" :: "'node \<Rightarrow> 'var set"
begin
  fun phiDefNodes_aux :: "'var \<Rightarrow> 'node list \<Rightarrow> 'node \<Rightarrow> 'node set" where
    "phiDefNodes_aux v unvisited n =(
        if n \<notin> set unvisited \<or> v \<in> defs n then {}
        else fold (op \<union>)
          [phiDefNodes_aux v (removeAll n unvisited) m . m \<leftarrow> predecessors n]
          (if length (predecessors n) \<noteq> 1 then {n} else {})
    )"

  definition phiDefNodes :: "'var \<Rightarrow> 'node set" where
    "phiDefNodes v \<equiv> fold (op \<union>)
      [phiDefNodes_aux v \<alpha>n n . n \<leftarrow> \<alpha>n, v \<in> uses n]
      {}"

  definition var :: " ('node, 'var) ssaVal \<Rightarrow> 'var" where "var \<equiv> fst"
  abbreviation defNode :: "('node, 'var) ssaVal \<Rightarrow> 'node" where "defNode \<equiv> snd"

  declare var_def[simp]

  function lookupDef :: "'node \<Rightarrow> 'var \<Rightarrow> ('node, 'var) ssaVal" where
    "lookupDef n v =(
        if n \<notin> set \<alpha>n then undefined
        else if v \<in> defs n then (v,n)
        else case predecessors n of
          [m] \<Rightarrow> lookupDef m v
          | _ \<Rightarrow> (v,n)
    )"
  by auto

  termination by (relation "measure (\<lambda>(n,_). shortestPath n)") (auto elim: shortestPath_single_predecessor)
  declare lookupDef.simps [code]

  definition defs' :: "'node \<Rightarrow> ('node, 'var) ssaVal set" where
    "defs' n \<equiv> (\<lambda>v. (v,n)) ` defs n"
  definition uses' :: "'node \<Rightarrow> ('node, 'var) ssaVal set" where
    "uses' n \<equiv> lookupDef n ` uses n"
  definition phis' :: " ('node, ('node, 'var) ssaVal) phis" where
    "phis' \<equiv> \<lambda>(n,(v,m)).
      if m = n \<and> n \<in> phiDefNodes v \<and> v \<in> vars then
        Some [lookupDef m v . m \<leftarrow> predecessors n]
      else None"
  declare uses'_def [code] defs'_def [code] phis'_def [code]

  abbreviation "lookupDefNode n v \<equiv> defNode (lookupDef n v)"
  declare lookupDef.simps [simp del]
  declare phiDefNodes_aux.simps [simp del]

  lemma phiDefNodes_aux_cases:
    obtains (nonrec) "phiDefNodes_aux v unvisited n = {}" "(n \<notin> set unvisited \<or> v \<in> defs n)"
    | (rec) "phiDefNodes_aux v unvisited n = fold union (map (phiDefNodes_aux v (removeAll n unvisited)) (predecessors n))
          (if length (predecessors n) = 1 then {} else {n})"
       "n \<in> set unvisited" "v \<notin> defs n"
  proof (cases "n \<in> set unvisited \<and> v \<notin> defs n")
    case True
    thus ?thesis using rec by (simp add:phiDefNodes_aux.simps)
  next
    case False
    thus ?thesis using nonrec by (simp add:phiDefNodes_aux.simps)
  qed

  lemma phiDefNode_aux_is_join_node:
    assumes "n \<in> phiDefNodes_aux v un m"
    shows "length (predecessors n) \<noteq> 1"
  using assms proof (induction un arbitrary: m rule:removeAll_induct)
    case (1 un m)
    thus ?case
    proof (cases un v m rule:phiDefNodes_aux_cases)
      case rec
      with 1 show ?thesis by (fastforce elim!:fold_union_elem split:split_if_asm)
    qed auto
  qed

  lemma phiDefNode_is_join_node:
    assumes "n \<in> phiDefNodes v"
    shows "length (predecessors n) \<noteq> 1"
  using assms unfolding phiDefNodes_def
  by (auto elim!:fold_union_elem dest!:phiDefNode_aux_is_join_node)

  abbreviation unvisitedPath :: "'node list \<Rightarrow> 'node list \<Rightarrow> bool" where
    "unvisitedPath un ns \<equiv> distinct ns \<and> set ns \<subseteq> set un"

  lemma unvisitedPath_removeLast:
    assumes "unvisitedPath un ns" "length ns \<ge> 2"
    shows "unvisitedPath (removeAll (last ns) un) (butlast ns)"
  proof-
    let ?n = "last ns"
    let ?ns' = "butlast ns"
    let ?un' = "removeAll ?n un"
    let ?n' = "last ?ns'"
    from assms(2) have [simp]: "?n = ns ! (length ns - 1)" by -(rule last_conv_nth, auto)
    from assms(1) have "distinct ?ns'" by -(rule distinct_butlast, simp)
    moreover
    have "set ?ns' \<subseteq> set ?un'"
    proof
      fix n
      assume assm: "n \<in> set ?ns'"
      then obtain i where "n = ?ns' ! i" "i < length ?ns'" by (auto simp add:in_set_conv_nth)
      hence i: "n = ns ! i" "i < length ns - 1" by (auto simp add:nth_butlast)
      with assms have 1: "n \<noteq> ?n" by (auto iff:nth_eq_iff_index_eq)
      from i assms(1) have "n \<in> set un" by auto
      with `n \<in> set ?ns'` assms(1) 1 show "n \<in> set ?un'" by auto
    qed
    ultimately show ?thesis by simp
  qed

  lemma phiDefNodes_auxI:
    assumes "n\<comment>ns\<rightarrow>m" "unvisitedPath un ns" "\<forall>n \<in> set ns. v \<notin> defs n" "length (predecessors n) \<noteq> 1"
    shows "n \<in> phiDefNodes_aux v un m"
  using assms(1,2,3) proof (induction un arbitrary: m ns rule:removeAll_induct)
    case (1 un)
    show ?case
    proof (cases un v m rule:phiDefNodes_aux_cases)
      case nonrec
      from "1.prems"(1) have "m \<in> set ns" unfolding path2_def by auto
      with nonrec show ?thesis using "1.prems"(2,3) by auto
    next
      case rec
      show ?thesis
      proof (cases "n = m")
        case True
        thus ?thesis using rec assms(4) by -(subst rec(1), rule fold_union_elemI[of _ "{m}"], auto)
      next
        case False
        let ?ns' = "butlast ns"
        let ?m' = "last ?ns'"
        from "1.prems"(1) have [simp]: "m = last ns" unfolding path2_def by simp
        with 1(2) False have ns': "n\<comment>?ns'\<rightarrow>?m'" "?m' \<in> set (predecessors m)" by (auto intro: path2_unsnoc)

        have "n \<in> phiDefNodes_aux v (removeAll m un) ?m'"
        using rec(2) ns'
        apply-
        proof (rule "1.IH")
          from "1.prems"(1) False have "length ns \<ge> 2" by (auto simp del:`m = last ns`)
          with "1.prems"(2) show "unvisitedPath (removeAll m un) ?ns'" by (subst `m = last ns`, rule unvisitedPath_removeLast)
          from "1.prems"(3) show "\<forall>n \<in> set ?ns'. v \<notin> defs n" by (auto intro:in_set_butlastD)
        qed
        with ns'(2) show ?thesis by -(subst rec, rule fold_union_elemI, auto)
      qed
    qed
  qed

  lemma phiDefNodes_auxE:
    assumes "n \<in> phiDefNodes_aux v un m" "m \<in> set \<alpha>n"
    obtains ns where "n\<comment>ns\<rightarrow>m" "\<forall>n \<in> set ns. v \<notin> defs n" "length (predecessors n) \<noteq> 1" "unvisitedPath un ns"
  using assms proof (atomize_elim, induction un arbitrary:m rule:removeAll_induct)
    case (1 un)
    show ?case
    proof (cases un v m rule:phiDefNodes_aux_cases)
      case nonrec
      thus ?thesis using "1.prems" by simp
    next
      case rec
      show ?thesis
      proof (cases "n \<in> (if length (predecessors m) = 1 then {} else {m})")
        case True
        hence "n = m" by (simp split:split_if_asm)
        thus ?thesis using "1.prems"(2) rec True by auto
      next
        case False
        with rec "1.prems"(1) obtain m' where m': "n \<in> phiDefNodes_aux v (removeAll m un) m'" "m' \<in> set (predecessors m)"
          by (auto elim!:fold_union_elem)
        with "1.prems"(2) have "m' \<in> set \<alpha>n" by auto
        with "1.IH"[of m m'] m' rec obtain ns where "n\<comment>ns\<rightarrow>m'" "\<forall>n \<in> set ns. v \<notin> defs n" "length (predecessors n) \<noteq> 1" "unvisitedPath (removeAll m un) ns" by auto
        thus ?thesis using m' rec by -(rule exI, auto)
      qed
    qed
  qed

  lemma phiDefNodesE:
    assumes "n \<in> phiDefNodes v"
    obtains ns m where "n\<comment>ns\<rightarrow>m" "v \<in> uses m" "\<forall>n \<in> set ns. v \<notin> defs n" "length (predecessors n) \<noteq> 1"
  using assms
  by (auto elim!:phiDefNodes_auxE elim!:fold_union_elem simp:phiDefNodes_def)

  lemma phiDefNodes_\<alpha>n[dest]: "n \<in> phiDefNodes v \<Longrightarrow> n \<in> set \<alpha>n"
  by (erule phiDefNodesE, auto)

  lemma phiDefNodesI:
    assumes "n\<comment>ns\<rightarrow>m" "v \<in> uses m" "\<forall>n \<in> set ns. v \<notin> defs n" "length (predecessors n) \<noteq> 1"
    shows "n \<in> phiDefNodes v"
  proof-
    from assms(1) have "m \<in> set \<alpha>n" by (rule path2_in_\<alpha>n, auto)
    from assms obtain ns' where "n\<comment>ns'\<rightarrow>m" "distinct ns'" "\<forall>n \<in> set ns'. v \<notin> defs n" by -(rule simple_path2, auto)
    with assms(4) have 1: "n \<in> phiDefNodes_aux v \<alpha>n m" by -(rule phiDefNodes_auxI, auto intro:path2_in_\<alpha>n)
    thus ?thesis using assms(2) `m \<in> set \<alpha>n`
    unfolding phiDefNodes_def
    by -(rule fold_union_elemI, auto)
  qed

 lemma phiDefNodes:
    "n \<in> phiDefNodes v \<longleftrightarrow> (\<exists>ns m. n\<comment>ns\<rightarrow>m \<and> v \<in> uses m \<and> (\<forall>n \<in> set ns. v \<notin> defs n) \<and> length (predecessors n) \<noteq> 1)"
  by (auto intro!: phiDefNodesI exI elim!: phiDefNodesE)

  lemma lookupDef_cases[consumes 1]:
    assumes "n \<in> set \<alpha>n"
    obtains (SimpleDef) "v \<in> defs n" "lookupDef n v = (v,n)"
          | (PhiDef)    "v \<notin> defs n" "length (predecessors n) \<noteq> 1" "lookupDef n v = (v,n)"
          | (rec) m where "v \<notin> defs n" "predecessors n = [m]" "m \<in> set \<alpha>n" "lookupDef n v = lookupDef m v"
  proof (cases "v \<in> defs n")
    case True
    thus thesis using assms SimpleDef by (simp add:lookupDef.simps)
  next
    case False
    thus thesis
    proof (cases "length (predecessors n) = 1")
      case True
      then obtain m where m: "predecessors n = [m]" by (cases "predecessors n", auto)
      hence "m \<in> set (predecessors n)" by simp
      thus thesis using False rec assms m by -(subst(asm) lookupDef.simps, drule predecessor_is_node, auto)
    next
      case False
      thus thesis using `v \<notin> defs n` assms by -(rule PhiDef, assumption, assumption, subst lookupDef.simps, auto split:list.split)
    qed
  qed

  lemma lookupDef_cases'[consumes 1]:
    assumes "n \<in> set \<alpha>n"
    obtains (SimpleDef) "v \<in> defs n" "defNode (lookupDef n v) = n"
          | (PhiDef)    "v \<notin> defs n" "length (predecessors n) \<noteq> 1" "lookupDefNode n v = n"
          | (rec) m where "v \<notin> defs n" "predecessors n = [m]" "m \<in> set \<alpha>n" "lookupDef n v = lookupDef m v"
  using assms
  by (rule lookupDef_cases[of n v]) simp_all

  lemma lookupDefE:
    assumes "lookupDef n v = v'" "n \<in> set \<alpha>n"
    obtains (SimpleDef) "v \<in> defs n" "v' = (v,n)"
          | (PhiDef)    "v \<notin> defs n" "length (predecessors n) \<noteq> 1" "v' = (v,n)"
          | (rec) m where "v \<notin> defs n" "predecessors n = [m]" "m \<in> set \<alpha>n" "v' = lookupDef m v"
  using assms by -(atomize_elim, cases rule:lookupDef_cases[of n v], auto)

  lemma lookupDef_induct[consumes 1, case_names SimpleDef PhiDef rec]:
    assumes "n \<in> set \<alpha>n"
            "\<And>n. \<lbrakk>n \<in> set \<alpha>n; v \<in> defs n; lookupDef n v = (v,n)\<rbrakk> \<Longrightarrow> P n"
            "\<And>n. \<lbrakk>n \<in> set \<alpha>n; v \<notin> defs n; length (predecessors n) \<noteq> 1; lookupDef n v = (v,n)\<rbrakk> \<Longrightarrow> P n"
            "\<And>n m. \<lbrakk>v \<notin> defs n; predecessors n = [m]; m \<in> set \<alpha>n; lookupDef n v = lookupDef m v; P m\<rbrakk> \<Longrightarrow> P n"
    shows "P n"
  apply (induct rule:lookupDef.induct[where P = "\<lambda>n v'. v'=v \<and> n \<in> set \<alpha>n \<longrightarrow> P n", of v n, simplified (no_asm), THEN mp])
   apply clarsimp
   apply (rule_tac v=v and n=n in lookupDef_cases; auto intro: assms lookupDef_cases)
  by (rule assms(1))

  lemma lookupDef_induct'[consumes 2, case_names SimpleDef PhiDef rec]:
    assumes "n \<in> set \<alpha>n" "lookupDef n v = (v,n')"
            "\<lbrakk>v \<in> defs n'\<rbrakk> \<Longrightarrow> P n'"
            "\<lbrakk>v \<notin> defs n'; length (predecessors n') \<noteq> 1\<rbrakk> \<Longrightarrow> P n'"
            "\<And>n m. \<lbrakk>v \<notin> defs n; predecessors n = [m]; m \<in> set \<alpha>n; lookupDef n v = lookupDef m v; P m\<rbrakk> \<Longrightarrow> P n"
    shows "P n"
    using assms(1,2)
    proof (induction rule:lookupDef_induct[where v=v])
      case (SimpleDef n)
      with assms(2) have "n = n'" by auto
      with SimpleDef assms(3) show ?case by simp
    next
      case (PhiDef n)
      with assms(2) have "n = n'" by auto
      with PhiDef assms(4) show ?case by simp
    qed (rule assms(5), simp_all)

  lemma lookupDef_looksup[dest?]:
    assumes "lookupDef n v = (v',n')" "n \<in> set \<alpha>n"
    shows "v' = v"
  using assms(1) assms(2) by (induction rule:lookupDef.induct) (auto elim:lookupDefE)

  lemma lookupDef_looksup':
    assumes "(v',n') = lookupDef n v" "n \<in> set \<alpha>n"
    shows "v' = v"
  using assms(1)[symmetric] assms(2) by (rule lookupDef_looksup)

  lemma lookupDef_looksup'':
    assumes "n \<in> set \<alpha>n"
    obtains n' where "lookupDef n v = (v,n')"
  apply atomize_elim
  using assms by (induction rule:lookupDef.induct) (cases rule:lookupDef_cases, auto)

  lemma lookupDef_fst[simp]: "n \<in> set \<alpha>n \<Longrightarrow> fst (lookupDef n v) = v"
  by (metis fst_conv lookupDef_looksup'')

  lemma lookupDef_to_\<alpha>n:
    assumes "lookupDef n v = (v',n')" "n \<in> set \<alpha>n"
    shows "n' \<in> set \<alpha>n"
  using assms(2,1)
  by (induction rule:lookupDef_induct[of n v]) simp_all

  lemma lookupDef_to_\<alpha>n':
    assumes "lookupDef n v = val" "n \<in> set \<alpha>n"
    shows "defNode val \<in> set \<alpha>n"
  using assms by (cases val) (auto simp:lookupDef_to_\<alpha>n)

  lemma lookupDef_induct''[consumes 2, case_names SimpleDef PhiDef rec]:
    assumes "lookupDef n v = val" "n \<in> set \<alpha>n"
            "\<lbrakk>v \<in> defs (defNode val)\<rbrakk> \<Longrightarrow> P (defNode val)"
            "\<lbrakk>v \<notin> defs (defNode val); length (predecessors (defNode val)) \<noteq> 1\<rbrakk> \<Longrightarrow> P (defNode val)"
            "\<And>n m. \<lbrakk>v \<notin> defs n; predecessors n = [m]; m \<in> set \<alpha>n; lookupDef n v = lookupDef m v; P m\<rbrakk> \<Longrightarrow> P n"
    shows "P n"
  using assms
  apply (cases val)
  apply (simp)
  apply (erule lookupDef_induct')
  using assms(2) by (auto dest: lookupDef_looksup)

  sublocale braun_ssa: CFG_SSA_base \<alpha>n predecessors Entry defs' uses' phis'
    by unfold_locales

  lemma defs'_finite: "finite (defs' n)"
  unfolding defs'_def using defs_finite
  by simp

  lemma uses'_finite: "finite (uses' n)"
  unfolding uses'_def using uses_finite
  by simp

  lemma defs'_uses'_disjoint: "n \<in> set \<alpha>n \<Longrightarrow> defs' n \<inter> uses' n = {}"
  unfolding defs'_def uses'_def using defs_uses_disjoint
  by (auto dest:lookupDef_looksup')

  lemma allDefs'_disjoint: " n \<in> set \<alpha>n \<Longrightarrow> m \<in> set \<alpha>n \<Longrightarrow> n \<noteq> m
    \<Longrightarrow> braun_ssa.allDefs n \<inter> braun_ssa.allDefs m = {}"
  by (auto split:split_if_asm simp: defs'_def phis'_def "CFG_SSA_base.CFG_SSA_defs")

  lemma phiDefNodes_aux_finite: "finite (phiDefNodes_aux v un m)"
  proof (induction un arbitrary:m rule:removeAll_induct)
    case (1 un)
    thus ?case by (cases un v m rule:phiDefNodes_aux_cases) auto
  qed

  lemma phis'_finite: "finite (dom (phis'))"
  proof-
    let ?super = "set \<alpha>n \<times> vars \<times> set \<alpha>n"
    have "finite ?super" by auto
    thus ?thesis
    by - (rule finite_subset[of _ ?super], auto simp:phis'_def split:split_if_asm)
  qed

  lemma phis'_wf: "phis' (n, v) = Some args \<Longrightarrow> length (predecessors n) = length args"
  unfolding phis'_def by (auto split:prod.splits split_if_asm)

  lemma simpleDefs_phiDefs_disjoint: "n \<in> set \<alpha>n \<Longrightarrow> defs' n \<inter> braun_ssa.phiDefs n = {}"
  unfolding braun_ssa.phiDefs_def
  unfolding phis'_def defs'_def
  by (auto elim!: phiDefNodesE dest!: path2_hd_in_ns split: split_if_asm)

  lemma oldDefs_correct: "defs n = var ` defs' n"
  by (simp add:defs'_def image_image)

  lemma oldUses_correct: "n \<in> set \<alpha>n \<Longrightarrow> uses n = var ` uses' n"
  by (simp add:uses'_def image_image)

  sublocale braun_ssa: CFG_SSA \<alpha>n predecessors Entry defs' uses' phis'
  apply unfold_locales
          apply (rule defs'_uses'_disjoint, simp_all)
         apply (rule defs'_finite)
        apply (auto simp add: uses'_def uses_in_\<alpha>n)[1]
       apply (rule uses'_finite)
      apply (rule phis'_finite)
     apply (auto simp: phis'_def split: split_if_asm)[1]
    apply (erule phis'_wf)
   apply (erule simpleDefs_phiDefs_disjoint)
  by (erule allDefs'_disjoint)
end

context CFG_Construct
begin
  lemma no_disjoint_cycle[simp]:
    assumes "n\<comment>ns\<rightarrow>n" "distinct ns"
    shows "ns = [n]"
  using assms unfolding path2_def
  by (metis distinct.simps(2) hd_Cons_tl last_in_set last_tl path_not_Nil)

  lemma lookupDef_path:
    assumes "m \<in> set \<alpha>n"
    obtains ns where  "lookupDefNode m v\<comment>ns\<rightarrow>m" "(\<forall>x \<in> set (tl ns). v \<notin> defs x)"
  apply atomize_elim
  using assms proof (induction rule:lookupDef_induct[of m v])
    case (SimpleDef n)
    thus ?case by -(rule exI[of _ "[n]"], auto)
  next
    case (PhiDef n)
    thus ?case by -(rule exI[of _ "[n]"], auto)
  next
    case (rec m m')
    then obtain ns where "lookupDefNode m v\<comment>ns\<rightarrow>m'" "\<forall>x \<in> set (tl ns). v \<notin> defs x" by auto
    with rec.hyps(1,2) show ?case by - (rule exI[of _ "ns@[m]"], auto simp: path2_not_Nil)
  qed

  lemma lookupDef_path_conventional:
    assumes "n\<comment>ns\<rightarrow>m" "n = lookupDefNode m v" "n \<notin> set (tl ns)" "x \<in> set (tl ns)" "v' \<in> braun_ssa.allDefs x"
    shows "var v' \<noteq> v"
  using assms(1-4) proof (induction rule:path2_rev_induct)
    case empty
    from empty.prems(3) have False by simp
    thus ?case ..
  next
    case (snoc ns m m')
    note snoc.prems(1)[simp]
    from snoc.hyps have p: "n\<comment>ns@[m']\<rightarrow>m'" by auto
    hence "m' \<in> set \<alpha>n" by auto
    thus ?thesis
    proof (cases rule:lookupDef_cases'[of m' v])
      case SimpleDef
      with snoc.prems(2,3) have False by (simp add:tl_append split:list.split_asm)
      thus ?thesis ..
    next
      case PhiDef
      with snoc.prems(2,3) have False by (simp add:tl_append split:list.split_asm)
      thus ?thesis ..
    next
      case (rec m\<^sub>2)
      from this(2) snoc.hyps(2) have[simp]: "m\<^sub>2 = m" by simp
      show ?thesis
      proof (cases "x \<in> set (tl ns)")
        case True
        with rec(4) snoc.prems(2) show ?thesis by - (rule snoc.IH, simp_all add:tl_append split:list.split_asm)
      next
        case False
        with snoc.prems(3) have[simp]: "x = m'" by (simp add:tl_append split:list.split_asm)

        show ?thesis
        proof (cases "v' \<in> defs' x")
          case True
          with rec(1) show ?thesis by (auto simp add:defs'_def)
        next
          case False
          with assms(5) have "v' \<in> braun_ssa.phiDefs m'" by (simp add:braun_ssa.allDefs_def)
          hence "m' \<in> phiDefNodes (fst v')"
            unfolding braun_ssa.phiDefs_def by (auto simp add: phis'_def split:prod.split_asm split_if_asm)
          with rec(2) show ?thesis by (auto dest:phiDefNode_is_join_node)
        qed
      qed
    qed
  qed

  lemma allUse_lookupDef:
    assumes "v \<in> braun_ssa.allUses m" "m \<in> set \<alpha>n"
    shows "lookupDef m (var v) = v"
  proof (cases "v \<in> uses' m")
    case True
    then obtain v' where v': "v = lookupDef m v'" "v' \<in> uses m" by (auto simp add:uses'_def)
    with assms(2) have "var v = v'" unfolding var_def by (metis lookupDef_fst)
    with v' show ?thesis by simp
  next
    case False
    with assms(1) obtain  m' v' vs where "(m,v) \<in> set (zip (predecessors m') vs)" "phis' (m', v') = Some vs"
      by (auto simp add:braun_ssa.allUses_def elim:braun_ssa.phiUsesE)
    hence l: "v = lookupDef m (var v')" by (auto simp add:phis'_def split:prod.split_asm split_if_asm elim:in_set_zip_map)
    with assms(2) have "var v = var v'" unfolding var_def by (metis lookupDef_fst)
    with l show ?thesis by simp
  qed

  lemma phis'_fst:
    assumes "phis' (n,v) = Some vs" "v' \<in> set vs"
    shows "var v' = var v"
  using assms by (auto intro!:lookupDef_fst dest!:phiDefNodes_\<alpha>n simp add:phis'_def split:prod.split_asm split_if_asm)

  lemma allUse_simpleUse:
    assumes "v \<in> braun_ssa.allUses m" "m \<in> set \<alpha>n"
    obtains ms m' where "m\<comment>ms\<rightarrow>m'" "var v \<in> uses m'" "\<forall>x \<in> set (tl ms). var v \<notin> defs x"
  proof (cases "v \<in> uses' m")
    case True
    then obtain v' where v': "v = lookupDef m v'" "v' \<in> uses m" by (auto simp add:uses'_def)
    with assms(2) have "var v = v'" unfolding var_def by (metis lookupDef_fst)
    with v' assms(2) show ?thesis by - (rule that, auto)
  next
    case False
    with assms(1) obtain  m' v' vs where phi: "(m,v) \<in> set (zip (predecessors m') vs)" "phis' (m', v') = Some vs"
      by (auto simp add:braun_ssa.allUses_def elim:braun_ssa.phiUsesE)
    hence m': "m' \<in> phiDefNodes (var v')" by (auto simp add:phis'_def split:prod.split_asm split_if_asm)
    from phi have[simp]: "var v = var v'" by - (rule phis'_fst, auto)
    from m' obtain m'' ms where "m'\<comment>ms\<rightarrow>m''" "\<forall>x \<in> set ms. var v' \<notin> defs x" "var v' \<in> uses m''" by (rule phiDefNodesE)
    with phi(1) show ?thesis by - (rule that[of "m#ms" m''], auto simp del:var_def)
  qed

  lemma defs': "v \<in> defs' n \<longleftrightarrow> var v \<in> defs n \<and> defNode v = n"
  by (cases v, auto simp add:defs'_def)

  lemma use_implies_allDef:
    assumes "lookupDef m (var v) = v"  "m \<in> set \<alpha>n" "var v \<in> uses m'" "m\<comment>ms\<rightarrow>m'" "\<forall>x \<in> set (tl ms). var v \<notin> defs x"
    shows "v \<in> braun_ssa.allDefs (defNode v)"
  using assms proof (induction arbitrary:ms rule:lookupDef_induct'')
      case SimpleDef
      hence "v \<in> defs' (defNode v)" by (simp add:defs')
      thus ?case by (simp add:braun_ssa.allDefs_def)
    next
      case PhiDef
      from PhiDef.prems(1,2) have vars: "var v \<in> vars" by auto
      from PhiDef.hyps(1) PhiDef.prems(2,3) have "\<forall>n\<in>set ms. var v \<notin> defs n" by (metis hd_Cons_tl path2_def path2_not_Nil set_ConsD)
      with PhiDef have "defNode v \<in> phiDefNodes (var v)" by - (rule phiDefNodesI)
      with vars have "v \<in> braun_ssa.phiDefs (defNode v)" unfolding braun_ssa.phiDefs_def by (auto simp add: phis'_def split: prod.split)
      thus ?case by (simp add:braun_ssa.allDefs_def)
    next
      case (rec n m)
      from rec.hyps(1) rec.prems(2,3) have "\<forall>n\<in>set ms. var v \<notin> defs n" by (metis hd_Cons_tl path2_def path2_not_Nil set_ConsD)
      with rec show ?case by - (rule rec.IH[of "m#ms"], auto)
    qed

  lemma allUse_defNode_in_\<alpha>n:
    assumes "v \<in> braun_ssa.allUses m" "m \<in> set \<alpha>n"
    shows "defNode v \<in> set \<alpha>n"
  proof-
    let ?n = "defNode (lookupDef m (var v))"
    from assms(1,2) have l: "lookupDef m (var v) = v" by (rule allUse_lookupDef)
    from assms obtain ns where ns: "?n\<comment>ns\<rightarrow>m" by - (rule lookupDef_path, auto)
    with l show ?thesis by auto
  qed

  lemma allUse_implies_allDef:
    assumes "v \<in> braun_ssa.allUses m" "m \<in> set \<alpha>n"
    shows "v \<in> braun_ssa.allDefs (defNode v)"
  proof-
    let ?n = "defNode (lookupDef m (var v))"
    from assms(1,2) have l: "lookupDef m (var v) = v" by (rule allUse_lookupDef)
    from assms obtain ns where ns: "?n\<comment>ns\<rightarrow>m" "\<forall>x \<in> set (tl ns). var v \<notin> defs x" by - (rule lookupDef_path, auto)
    from assms obtain ms m' where "m\<comment>ms\<rightarrow>m'" "var v \<in> uses m'" "\<forall>x \<in> set (tl ms). var v \<notin> defs x" by - (rule allUse_simpleUse)
    hence "v \<in> braun_ssa.allDefs (defNode v)" using ns assms(2) l by - (rule use_implies_allDef, auto)
    with assms(2) l show ?thesis by simp
  qed

  lemma conventional:
    assumes "n\<comment>ns\<rightarrow>m" "n \<notin> set (tl ns)" "v \<in> braun_ssa.allDefs n" "v \<in> braun_ssa.allUses m"
      "x \<in> set (tl ns)" "v' \<in> braun_ssa.allDefs x"
    shows "var v' \<noteq> var v"
  proof-
    from assms(1) have[simp]: "m \<in> set \<alpha>n" by auto
    from assms(4) have[simp]: "lookupDef m (var v) = v" by - (rule allUse_lookupDef, auto)

    from assms(1,4) have "v \<in> braun_ssa.allDefs (defNode v)" by - (rule allUse_implies_allDef, auto)
    with assms(1,3,4) braun_ssa.allDefs_disjoint[of n "defNode v"] have[simp]: "defNode v = n" by - (rule braun_ssa.allDefs_disjoint', auto elim: allUse_defNode_in_\<alpha>n)

    from assms show ?thesis by - (rule lookupDef_path_conventional[where m=m], simp_all add:uses'_def del:var_def)
  qed

  lemma allDefs_var_disjoint_aux: "n \<in> set \<alpha>n \<Longrightarrow> v \<in> defs n \<Longrightarrow> n \<notin> phiDefNodes v"
    by (auto elim!:phiDefNodesE dest:path2_hd_in_ns)

  lemma allDefs_var_disjoint: "\<lbrakk>n \<in> set \<alpha>n; v \<in> braun_ssa.allDefs n; v' \<in> braun_ssa.allDefs n; v \<noteq> v'\<rbrakk> \<Longrightarrow> var v' \<noteq> var v"
    unfolding braun_ssa.allDefs_def braun_ssa.phiDefs_def
    by (auto simp: defs'_def phis'_def intro: allDefs_var_disjoint_aux split:prod.splits split_if_asm)

  lemma[simp]: "n \<in> set \<alpha>n \<Longrightarrow> v \<in> defs n \<Longrightarrow> lookupDefNode n v = n"
  by (cases rule:lookupDef_cases[of n v]) simp_all

  lemma[simp]: "n \<in> set \<alpha>n \<Longrightarrow> length (predecessors n) \<noteq> 1 \<Longrightarrow> lookupDefNode n v = n"
  by (cases rule:lookupDef_cases[of n v]) simp_all

  lemma lookupDef_idem[simp]:
    assumes "n \<in> set \<alpha>n"
    shows "lookupDef (lookupDefNode n v) v = lookupDef n v"
  using assms by (induction rule:lookupDef_induct''[of n v, OF refl]) (simp_all add:assms)
end

locale CFG_Construct_wf = CFG_Construct \<alpha>n predecessors Entry "defs" "uses" + CFG_wf \<alpha>n predecessors Entry "defs" "uses"
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  "defs" :: "'node \<Rightarrow> 'var::linorder set" and
  "uses" :: "'node \<Rightarrow> 'var set"
begin
  lemma def_ass_allUses_aux:
    assumes "Entry\<comment>ns\<rightarrow>n"
    shows "lookupDefNode n (var v) \<in> set ns"
  proof-
    from assms have[simp]: "n \<in> set \<alpha>n" by auto
    thus ?thesis using assms
    proof (induction arbitrary:ns rule:lookupDef_induct''[of n "var v", OF refl, consumes 1])
      case (3 m m' ns)
      show ?case
      proof (cases "length ns \<ge> 2")
        case False
        with "3.prems" have "m = Entry" by (metis path2_nontrivial)
        with "3.hyps"(2) have False by simp
        thus ?thesis ..
      next
        case True
        with "3.prems" have "Entry\<comment>butlast ns\<rightarrow>m'"
        by (rule path2_unsnoc) (simp add:"3.hyps"(2))
        with "3.hyps" "3.IH"[of "butlast ns"] show ?thesis by (simp add:in_set_butlastD)
      qed
    qed auto
  qed

  lemma def_ass_allUses:
    assumes "v \<in> braun_ssa.allUses n" "n \<in> set \<alpha>n"
    shows "braun_ssa.defAss n v"
  proof (rule braun_ssa.defAssI)
    fix ns
    assume asm: "Entry\<comment>ns\<rightarrow>n"
    let ?m = "lookupDefNode n (var v)"
    from asm have "?m \<in> set ns" by (rule def_ass_allUses_aux)
    moreover from assms allUse_lookupDef have "?m = defNode v" by simp
    moreover from assms allUse_implies_allDef have "v \<in> braun_ssa.allDefs (defNode v)" by simp
    ultimately show "\<exists>n\<in>set ns. v \<in> braun_ssa.allDefs n" by auto
  qed

  lemma Empty_no_phis:
    shows "phis' (Entry, v) = None"
  proof-
    have "\<And>v. Entry \<notin> phiDefNodes v"
    proof (rule, rule phiDefNodesE, assumption)
      fix v ns m
      assume asm: "Entry\<comment>ns\<rightarrow>m" "\<forall>n\<in>set ns. v \<notin> defs n" "v \<in> uses m"
      hence "m \<in> set \<alpha>n" by auto
      from def_ass_uses[of, THEN bspec[OF _ this], THEN bspec[OF _ asm(3)]] asm
      show False by (auto elim!:defAss'E)
    qed
    thus ?thesis by (auto simp:phis'_def split:prod.split)
  qed

  lemma braun_ssa_CFG_SSA_wf:
    "CFG_SSA_wf \<alpha>n predecessors Entry defs' uses' phis'"
  apply unfold_locales
   apply (erule def_ass_allUses, assumption)
  apply (rule Empty_no_phis)
  done

  sublocale braun_ssa: CFG_SSA_wf \<alpha>n predecessors Entry defs' uses' phis'
  by (rule braun_ssa_CFG_SSA_wf)

  lemma braun_ssa_CFG_SSA_Transformed:
    "CFG_SSA_Transformed \<alpha>n predecessors Entry defs uses defs' uses' phis' var"
  apply unfold_locales
      apply (rule oldDefs_correct)
     apply (erule oldUses_correct)
    apply (erule conventional, simp, simp, simp, simp, simp)
   apply (erule phis'_fst, simp)
  apply (erule allDefs_var_disjoint, simp, simp, simp)
  done

  sublocale braun_ssa: CFG_SSA_Transformed \<alpha>n predecessors Entry "defs" "uses" defs' uses' phis' var
  by (rule braun_ssa_CFG_SSA_Transformed)

  lemma PhiDef_defNode_eq:
    assumes "n \<in> set \<alpha>n" "n \<in> phiDefNodes v" "v \<in> vars"
    shows "braun_ssa.defNode (v,n) = n"
  using assms by - (rule braun_ssa.defNode_eq, rule assms(1), subst braun_ssa.allDefs_def, subst braun_ssa.phiDefs_def, auto simp: phis'_def)

  lemma phiDefNodes_aux_pruned_aux:
    assumes "n \<in> phiDefNodes_aux v \<alpha>n nUse" "v \<in> uses nUse" "n\<comment>ns\<rightarrow>m" "m\<comment>ms\<rightarrow>nUse" "braun_ssa.liveVal (lookupDef m v)" "\<forall>n \<in> set (ns@ms). v \<notin> defs n"
    shows "braun_ssa.liveVal (v,n)"
  using assms(3-) proof (induction n ns m arbitrary:ms rule:path2_rev_induct)
    case empty
    with assms(1) have "lookupDef n v = (v,n)"
      by -(drule phiDefNode_aux_is_join_node, cases rule:lookupDef_cases, auto)
    with empty.prems(2) show ?case by simp
  next
    case (snoc ns m m')
    from snoc.prems have "m' \<in> set \<alpha>n" by auto
    thus ?case
    proof (cases rule:lookupDef_cases[where v=v])
      case SimpleDef
      with snoc.prems(3) have False by simp
      thus ?thesis..
    next
      have step: "braun_ssa.liveVal (lookupDef m v) \<Longrightarrow> ?thesis"
      proof (rule snoc.IH)
        from snoc.prems(1) snoc.hyps(2) show "m\<comment>m#ms\<rightarrow>nUse" by auto
        from snoc.prems(3) snoc.hyps(1) show "\<forall>n\<in> set(ns @ m # ms). v \<notin> defs n" by auto
      qed
      {
        case rec
        from snoc.hyps(2) rec(2) have[simp]: "predecessors m' = [m]" by auto
        with rec snoc.prems(2) have "braun_ssa.liveVal (lookupDef m v)" by auto
        with step show ?thesis.
      next
        case PhiDef
        with snoc assms(2) have phiDefNode: "m' \<in> phiDefNodes v" by -(rule phiDefNodesI, auto)
        from assms(2,4) have vars: "v \<in> vars" by auto
        have "braun_ssa.liveVal (lookupDef m v)"
        proof (rule braun_ssa.livePhi)
          from PhiDef(3) snoc.prems(2) show "braun_ssa.liveVal (v,m')" by simp
          from phiDefNode snoc.hyps(2) vars show "braun_ssa.phiArg (v,m') (lookupDef m v)"
            by (subst braun_ssa.phiArg_def, subst braun_ssa.phi_def, subst PhiDef_defNode_eq, auto simp: phis'_def)
        qed
        thus ?thesis by (rule step)
      }
    qed
  qed

  lemma phiDefNodes_aux_pruned:
    assumes "m \<in> phiDefNodes_aux v \<alpha>n n" "n \<in> set \<alpha>n" "v \<in> uses n"
    shows "braun_ssa.liveVal (v, m)"
  proof-
    from assms(1,2) obtain ns where ns: "m\<comment>ns\<rightarrow>n" "\<forall>n \<in> set ns. v \<notin> defs n" by (rule phiDefNodes_auxE)
    hence "v \<notin> defs n" by (auto dest:path2_last simp: path2_not_Nil)
    with ns assms(1,3) show ?thesis
    apply-
    proof (rule phiDefNodes_aux_pruned_aux)
      from assms(2,3) show "braun_ssa.liveVal (lookupDef n v)" by -(rule braun_ssa.liveSimple, auto simp add:uses'_def)
    qed auto
  qed

  theorem phis'_pruned: "braun_ssa.pruned"
  unfolding braun_ssa.pruned_def braun_ssa.phiDefs_def
  apply (subst phis'_def)
  by (auto split:prod.splits split_if_asm simp add:phiDefNodes_def elim!:fold_union_elem phiDefNodes_aux_pruned)

  declare var_def[simp del]

  declare no_disjoint_cycle [simp del]

  declare lookupDef.simps [code]
  declare phiDefNodes_aux.simps [code]
  declare phiDefNodes_def [code]
  declare defs'_def [code]
  declare uses'_def [code]
  declare phis'_def [code]
end

end
