(*  Title:      Construct_SSA_notriv_code.thy
    Author:     Sebastian Ullrich, Denis Lohner
*)

subsection {* Inductive Removal of Trivial Phi Functions *}

theory Construct_SSA_notriv
imports SSA_CFG Minimality "~~/src/HOL/Library/While_Combinator"
begin

locale CFG_SSA_Transformed_notriv_base = CFG_SSA_Transformed_base \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  oldDefs :: "'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'node \<Rightarrow> 'var set" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'node \<Rightarrow> 'val set" and
  phis :: " ('node, 'val) phis" and
  var :: "'val \<Rightarrow> 'var" +
fixes chooseNext_all :: "('node \<Rightarrow> 'val set) \<Rightarrow> ('node, 'val) phis \<Rightarrow> ('node \<times> 'val)"
begin
  abbreviation "chooseNext \<equiv> snd (chooseNext_all uses phis)"
  abbreviation "chooseNext' \<equiv> chooseNext_all uses phis"

  definition "substitution \<equiv> THE v'. isTrivialPhi (chooseNext) v'"
  definition "substNext \<equiv> \<lambda>v. if v = chooseNext then substitution else v"
  definition[simp]: "uses' n \<equiv> substNext ` uses n"
  definition[simp]: "phis' x \<equiv> case x of (n,v) \<Rightarrow> if v = chooseNext
    then None
    else map_option (map (substNext)) (phis (n,v))"
end

locale CFG_SSA_Transformed_notriv = CFG_SSA_Transformed \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var
  + CFG_SSA_Transformed_notriv_base \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  "oldDefs" :: "'node \<Rightarrow> 'var::linorder set" and
  "oldUses" :: "'node \<Rightarrow> 'var set" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'node \<Rightarrow> 'val set" and
  phis :: " ('node, 'val) phis" and
  var :: "'val \<Rightarrow> 'var" and
  chooseNext_all :: "('node \<Rightarrow> 'val set) \<Rightarrow> ('node, 'val) phis \<Rightarrow> ('node \<times> 'val)" +
assumes chooseNext_all: "CFG_SSA_Transformed \<alpha>n predecessors Entry oldDefs oldUses defs u p var \<Longrightarrow>
  CFG_SSA_wf_base.redundant \<alpha>n predecessors defs u p \<Longrightarrow>
  chooseNext_all (u) (p) \<in> dom (p) \<and>
  CFG_SSA_wf_base.trivial \<alpha>n predecessors defs u p (snd (chooseNext_all (u) (p)))"
begin
  lemma chooseNext':"redundant \<Longrightarrow> chooseNext' \<in> dom phis \<and> trivial (chooseNext)"
  by (rule chooseNext_all, unfold_locales)

  lemma chooseNext: "redundant \<Longrightarrow> chooseNext \<in> allVars \<and> trivial (chooseNext)"
  by (drule chooseNext', auto simp: trivial_in_allVars)

  lemmas chooseNext_in_allVars[simp] = chooseNext[THEN conjunct1]

  lemma isTrivialPhi_det: "trivial v \<Longrightarrow> \<exists>!v'. isTrivialPhi v v'"
  proof(rule ex_ex1I)
    fix v' v''
    assume "isTrivialPhi v v'" "isTrivialPhi v v''"
    from this[unfolded isTrivialPhi_def, THEN conjunct2] show "v' = v''" by (auto simp:isTrivialPhi_def doubleton_eq_iff split:option.splits)
  qed (auto simp: trivial_def)

  lemma trivialPhi_strict_dom:
    assumes[simp]: "v \<in> allVars" and triv: "isTrivialPhi v v'"
    shows "strict_def_dom v' v"
  proof
    let ?n = "defNode v"
    let ?n' = "defNode v'"
    from triv obtain vs where vs: "phi v = Some vs" "(set vs = {v'} \<or> set vs = {v,v'})" by (auto simp:isTrivialPhi_def split:option.splits)
    hence "?n \<noteq> Entry" by auto

    have other_preds_dominated: "\<And>m. m \<in> set (predecessors ?n) \<Longrightarrow> v' \<notin> phiUses m \<Longrightarrow> dominates ?n m"
    proof-
      fix m
      assume m: "m \<in> set (predecessors ?n)" "v' \<notin> phiUses m"
      hence[simp]: "m \<in> set \<alpha>n" by auto
      show "dominates ?n m"
      proof (cases "v \<in> phiUses m")
        case True
        hence "v \<in> allUses m" by simp
        thus ?thesis by (rule allUses_dominated) simp_all
      next
        case False
        with vs have  "v' \<in> phiUses m" by - (rule phiUses_exI[OF m(1)], auto simp:phi_def)
        with m(2) show ?thesis by simp
      qed
    qed

    show "?n' \<noteq> ?n"
    proof (rule notI)
      assume asm: "?n' = ?n"
      have "\<And>m. m \<in> set (predecessors ?n) \<Longrightarrow> v' \<in> phiUses m \<Longrightarrow> dominates ?n m"
      proof-
        fix m
        assume "m \<in> set (predecessors ?n)" "v' \<in> phiUses m"
        hence "dominates ?n' m" by - (rule allUses_dominated, auto)
        thus "?thesis m" by (simp add:asm)
      qed
      with non_dominated_predecessor[of ?n] other_preds_dominated `?n \<noteq> Entry` show False by auto
    qed

    show "dominates ?n' ?n"
    proof (rule dominatesI)
      fix ns
      assume asm: "Entry\<comment>ns\<rightarrow>?n"
      from `?n \<noteq> Entry` obtain m ns'
        where ns': "Entry\<comment>ns'\<rightarrow>m" "m \<in> set (predecessors ?n)" "?n \<notin> set ns'" "set ns' \<subseteq> set ns"
        by - (rule simple_path2_unsnoc[OF asm], auto)
      hence[simp]: "m \<in> set \<alpha>n" by auto
      from ns' have "\<not>dominates ?n m" by (auto elim:dominatesE)
      with other_preds_dominated[of m] ns'(2) have "v' \<in> phiUses m" by auto
      hence "dominates ?n' m" by - (rule allUses_dominated, auto)
      with ns'(1) have "?n' \<in> set ns'" by - (erule dominatesE)
      with ns'(4) show "?n' \<in> set ns" by auto
    qed auto
  qed

  lemma isTrivialPhi_asymmetric:
  assumes "isTrivialPhi a b"
    and "isTrivialPhi b a"
  shows "False"
  using assms
  proof -
    from `isTrivialPhi a b`
    have "b \<in> allVars"
      unfolding isTrivialPhi_def
      by (fastforce intro!: phiArg_in_allVars simp: phiArg_def split: option.splits)
    from `isTrivialPhi b a`
    have "a \<in> allVars"
      unfolding isTrivialPhi_def
      by (fastforce intro!: phiArg_in_allVars simp: phiArg_def split: option.splits)
    from trivialPhi_strict_dom [OF `a \<in> allVars` assms(1)]
       trivialPhi_strict_dom [OF `b \<in> allVars` assms(2)]
    show ?thesis by (auto dest: dominates_antisymm)
  qed

  lemma substitution[intro]: "redundant \<Longrightarrow> isTrivialPhi (chooseNext) (substitution)"
    unfolding substitution_def by (rule theI', rule isTrivialPhi_det, simp add: chooseNext)

  lemma trivialPhi_in_allVars[simp]:
    assumes "isTrivialPhi v v'" and[simp]: "v \<in> allVars"
    shows "v' \<in> allVars"
  proof-
    from assms(1) have "phiArg v v'"
      unfolding phiArg_def
      by (auto simp:isTrivialPhi_def split:option.splits)
    thus "v' \<in> allVars" by - (rule phiArg_in_allVars, auto)
  qed

  lemma substitution_in_allVars[simp]:
    assumes "redundant"
    shows "substitution \<in> allVars"
  using assms by - (rule trivialPhi_in_allVars, auto)

  lemma defs_uses_disjoint_inv:
    assumes[simp]: "n \<in> set \<alpha>n" "redundant"
    shows "defs n \<inter> uses' n = {}"
  proof (rule equals0I)
    fix v'
    assume asm: "v' \<in> defs n \<inter> uses' n"
    then obtain v where v: "v \<in> uses n" "v' = substNext v" and v': "v' \<in> defs n" by auto
    show False
    proof (cases "v = chooseNext")
      case False
      thus ?thesis using v v' defs_uses_disjoint[of n] by (auto simp:substNext_def split:split_if_asm)
    next
      case [simp]: True
      from v' have n_defNode: "n = defNode v'" by - (rule defNode_eq[symmetric], auto)
      from v(1) have[simp]: "v \<in> allVars" by - (rule allUses_in_allVars[where n=n], auto)
      let ?n' = "defNode v"
      have "strict_dom n ?n'"
        by (simp only:n_defNode v(2), rule trivialPhi_strict_dom, auto simp:substNext_def)
      moreover from v(1) have "dominates ?n' n" by - (rule allUses_dominated, auto)
      ultimately show False by - (drule dominates_antisymm, auto)
    qed
  qed
end

context CFG_SSA_wf
begin
  inductive liveVal' :: "'val list \<Rightarrow> bool"
  where
    liveSimple': "\<lbrakk>n \<in> set \<alpha>n; val \<in> uses n\<rbrakk> \<Longrightarrow> liveVal' [val]"
  | livePhi': "\<lbrakk>liveVal' (v#vs); phiArg v v'\<rbrakk> \<Longrightarrow> liveVal' (v'#v#vs)"

  lemma liveVal'_suffixeq:
    assumes "liveVal' vs" "suffixeq vs' vs" "vs' \<noteq> []"
    shows "liveVal' vs'"
  using assms proof induction
    case (liveSimple' n v)
    from liveSimple'.prems have "vs' = [v]"
      by (metis append_Nil butlast.simps(2) suffixeqI suffixeq_antisym suffixeq_unsnoc)
    with liveSimple'.hyps show ?case by (auto intro: liveVal'.liveSimple')
  next
    case (livePhi' v vs v')
    show ?case
    proof (cases "vs' = v' # v # vs")
      case True
      with livePhi' show ?thesis by - (auto intro: liveVal'.livePhi')
    next
      case False
      with livePhi'.prems have "suffixeq vs' (v#vs)"
        by (metis list.sel(3) self_append_conv2 suffixeqI suffixeq_take tl_append2)
      with livePhi'.prems(2) show ?thesis by - (rule livePhi'.IH)
    qed
  qed

  lemma liveVal'I:
    assumes "liveVal v"
    obtains vs where "liveVal' (v#vs)"
  using assms proof induction
    case (liveSimple n v)
    thus thesis by - (rule liveSimple(3), rule liveSimple')
  next
    case (livePhi v v')
    show thesis
    proof (rule livePhi.IH)
      fix vs
      assume asm: "liveVal' (v#vs)"
      show thesis
      proof (cases "v' \<in> set (v#vs)")
        case False
        with livePhi.hyps asm show thesis by - (rule livePhi.prems, rule livePhi')
      next
        case True
        then obtain vs' where "suffixeq (v'#vs') (v#vs)"
          by - (drule split_list_last, auto simp: suffixeq_def)
        with asm show thesis by - (rule livePhi.prems, rule liveVal'_suffixeq, simp_all)
      qed
    qed
  qed

  lemma liveVal'D:
    assumes "liveVal' vs" "vs = v#vs'"
    shows "liveVal v"
  using assms proof (induction arbitrary: v vs')
    case (liveSimple' n vs)
    thus ?case by - (rule liveSimple, auto)
  next
    case (livePhi' v\<^sub>2 vs v')
    thus ?case by - (rule livePhi, auto)
  qed
end

locale CFG_SSA_step = CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  "oldDefs" :: "'node \<Rightarrow> 'var::linorder set" and
  "oldUses" :: "'node \<Rightarrow> 'var set" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'node \<Rightarrow> 'val set" and
  phis :: " ('node, 'val) phis" and
  var :: "'val \<Rightarrow> 'var" and
  chooseNext_all :: "('node \<Rightarrow> 'val set) \<Rightarrow> ('node, 'val) phis \<Rightarrow> ('node \<times> 'val)" +
assumes redundant[simp]: "redundant"
begin
  sublocale step: CFG_SSA_Transformed_notriv_base \<alpha>n predecessors Entry oldDefs oldUses "defs" uses' phis' var chooseNext_all .

  lemma simpleDefs_phiDefs_disjoint_inv:
    assumes "n \<in> set \<alpha>n"
    shows "defs n \<inter> step.phiDefs n = {}"
  using simpleDefs_phiDefs_disjoint[OF assms]
  by (auto simp: phiDefs_def step.phiDefs_def dom_def split:option.splits)

  lemma allDefs_disjoint_inv:
    assumes "n \<in> set \<alpha>n" "m \<in> set \<alpha>n" "n \<noteq> m"
    shows "step.allDefs n \<inter> step.allDefs m = {}"
  using allDefs_disjoint[OF assms]
  by (auto simp: dom_def "CFG_SSA_base.CFG_SSA_defs" split:option.splits)

  lemma phis_finite_inv:
    shows "finite (dom (phis'))"
  using phis_finite[of] by - (rule finite_subset, auto split:split_if_asm)

  lemma phis_wf_inv:
    assumes "phis' (n, v) = Some args"
    shows "length (predecessors n) = length args"
  using phis_wf[of] assms by (auto split:split_if_asm)


  sublocale step: CFG_SSA \<alpha>n predecessors Entry "defs" uses' phis'
  apply unfold_locales
          apply (rule defs_uses_disjoint_inv; simp)
         apply (rule defs_finite)
        apply (auto simp: uses_in_\<alpha>n split: split_if_asm)[1]
       apply simp
      apply (simp add:phis_finite_inv)
     apply (auto simp: phis_in_\<alpha>n split: split_if_asm)[1]
    apply (simp add:phis_wf_inv)
   apply (simp add: simpleDefs_phiDefs_disjoint_inv)
  apply (simp add: allDefs_disjoint_inv)
  done

  lemma allUses_narrows:
    assumes "n \<in> set \<alpha>n"
    shows "step.allUses n \<subseteq> substNext ` allUses n"
  proof-
    have "\<And>n' v' z b. phis (n', v') = Some z \<Longrightarrow> (n, b) \<in> set (zip (predecessors n') z) \<Longrightarrow> b \<notin> phiUses n \<Longrightarrow> b \<in> uses n"
    proof-
      fix n' v' z b
      assume "(n, b) \<in> set (zip (predecessors n') (z :: 'val list))"
      with assms(1) have "n' \<in> set \<alpha>n" by auto
      thus "phis (n', v') = Some z \<Longrightarrow> (n, b) \<in> set (zip (predecessors n') z) \<Longrightarrow> b \<notin> phiUses n \<Longrightarrow> b \<in> uses n" by (auto intro:phiUsesI)
    qed
    thus ?thesis by (auto simp:step.allUses_def allUses_def zip_map2 intro!:imageI elim!:step.phiUsesE phiUsesE split:split_if_asm)
  qed

  lemma allDefs_narrows[simp]: "v \<in> step.allDefs n \<Longrightarrow> v \<in> allDefs n"
    by (auto simp:step.allDefs_def step.phiDefs_def phiDefs_def allDefs_def split:split_if_asm)

  lemma allUses_def_ass_inv:
    assumes "v' \<in> step.allUses n" "n \<in> set \<alpha>n"
    shows "step.defAss n v'"
  proof (rule step.defAssI)
    fix ns
    assume asm: "Entry\<comment>ns\<rightarrow>n"

    from assms obtain v where v': "v' = substNext v" and[simp]: "v \<in> allUses n"
      using allUses_narrows by auto
    with assms(2) have[simp]: "v \<in> allVars" by - (rule allUses_in_allVars)
    have[simp]: "v' \<in> allVars" by (simp add:substNext_def v')
    let ?n\<^sub>v = "defNode v"
    let ?n\<^sub>v\<^sub>' = "defNode v'"
    from assms(2) asm have 1: "?n\<^sub>v \<in> set ns" using allUses_def_ass[of v n] by (simp add:defAss_defNode)
    then obtain ns\<^sub>v where ns\<^sub>v: "prefixeq (ns\<^sub>v@[?n\<^sub>v]) ns" by (rule prefix_split_first)
    with asm have 2: "Entry\<comment>ns\<^sub>v@[?n\<^sub>v]\<rightarrow>?n\<^sub>v" by auto
    show "\<exists>n \<in> set ns. v' \<in> step.allDefs n"
    proof (cases "v = chooseNext")
      case True
      hence dom: "strict_def_dom v' v" using substitution[of] by - (rule trivialPhi_strict_dom, simp_all add:substNext_def v')
      hence[simp]: "v' \<noteq> v" by auto
      have "v' \<in> allDefs ?n\<^sub>v\<^sub>'" by simp
      hence "v' \<in> step.allDefs ?n\<^sub>v\<^sub>'" unfolding step.allDefs_def step.phiDefs_def allDefs_def phiDefs_def by (auto simp:True[symmetric])
      moreover have "?n\<^sub>v\<^sub>' \<in> set ns"
      proof-
        from dom have "def_dominates v' v" by auto
        hence "?n\<^sub>v\<^sub>' \<in> set (ns\<^sub>v@[?n\<^sub>v])" using 2 by -(erule dominatesE)
        with ns\<^sub>v show ?thesis by auto
      qed
      ultimately show ?thesis by auto
    next
      case [simp]: False
      have[simp]: "v' = v" by (simp add:v' substNext_def)
      have "v \<in> allDefs ?n\<^sub>v" by simp
      thus ?thesis by - (rule bexI[of _ ?n\<^sub>v\<^sub>'], auto simp:allDefs_def step.allDefs_def step.phiDefs_def 1 phiDefs_def)
    qed
  qed

  lemma Entry_no_phis_inv: "phis' (Entry, v) = None"
  by (simp add:Entry_no_phis)

  sublocale step: CFG_SSA_wf \<alpha>n predecessors Entry "defs" uses' phis'
  apply unfold_locales
   apply (simp add:allUses_def_ass_inv)
  apply (simp add:Entry_no_phis_inv)
  done

  lemma chooseNext_eliminated: "chooseNext \<notin> step.allDefs (defNode (chooseNext))"
  proof-
    let ?v = "chooseNext"
    let ?n = "defNode ?v"
    from chooseNext[OF redundant] have "?v \<in> phiDefs ?n" "?n \<in> set \<alpha>n"
      by (auto simp: trivial_def isTrivialPhi_def phiDefs_def phi_def split: option.splits)
    hence "?v \<notin> defs ?n" using simpleDefs_phiDefs_disjoint[of ?n] by auto
    thus ?thesis by (auto simp:step.allDefs_def step.phiDefs_def)
  qed

  lemma oldUses_inv:
    assumes "n \<in> set \<alpha>n"
    shows "oldUses n = var ` uses' n"
  proof-
    have "var (substitution) = var (chooseNext)" using substitution[of]
      by - (rule phiArg_same_var, auto simp: isTrivialPhi_def phiArg_def split: option.splits)
    thus ?thesis using assms by (auto simp: substNext_def oldUses_def image_Un)
  qed

  lemma conventional_inv:
    assumes "n\<comment>ns\<rightarrow>m" "n \<notin> set (tl ns)" "v \<in> step.allDefs n" "v \<in> step.allUses m" "x \<in> set (tl ns)" "v' \<in> step.allDefs x"
    shows "var v' \<noteq> var v"
  proof-
    from assms(1,3) have[simp]: "n = defNode v" "v \<in> allDefs n" by - (rule defNode_eq[symmetric], auto)
    from assms(1) have[simp]: "m \<in> set \<alpha>n" by auto
    from assms(4) obtain v\<^sub>0 where v\<^sub>0: "v = substNext v\<^sub>0" "v\<^sub>0 \<in> allUses m" using allUses_narrows[of m] by auto
    hence[simp]: "v\<^sub>0 \<in> allVars" using assms(1) by auto
    let ?n\<^sub>0 = "defNode v\<^sub>0"
    show ?thesis
    proof (cases "v\<^sub>0 = chooseNext")
      case False
      with v\<^sub>0 have "v = v\<^sub>0" by (simp add:substNext_def split:split_if_asm)
      with assms v\<^sub>0 show ?thesis by - (rule conventional, auto)
    next
      case True
      hence dom: "strict_def_dom v v\<^sub>0" using substitution[of] by - (rule trivialPhi_strict_dom, simp_all add:substNext_def v\<^sub>0)
      from v\<^sub>0(2) have "dominates ?n\<^sub>0 m" using assms(1) by - (rule allUses_dominated, auto)
      with assms(1) dom have "?n\<^sub>0 \<in> set ns" by - (rule dominates_mid, auto)
      with assms(1) obtain ns\<^sub>1 ns\<^sub>3 ns\<^sub>2 where
        ns: "ns = ns\<^sub>1@ns\<^sub>3@ns\<^sub>2" and
        ns\<^sub>1: "n\<comment>ns\<^sub>1@[?n\<^sub>0]\<rightarrow>?n\<^sub>0"  "?n\<^sub>0 \<notin> set ns\<^sub>1" and
        ns\<^sub>3: "?n\<^sub>0\<comment>ns\<^sub>3\<rightarrow>?n\<^sub>0" and
        ns\<^sub>2: "?n\<^sub>0\<comment>?n\<^sub>0#ns\<^sub>2\<rightarrow>m" "?n\<^sub>0 \<notin> set ns\<^sub>2" by (rule path2_split_first_last)
      have[simp]: "ns\<^sub>1 \<noteq> []"
      proof
        assume "ns\<^sub>1 = []"
        hence "?n\<^sub>0 = n" "hd ns = n" using assms(1) ns\<^sub>3 by (auto simp:ns path2_def)
        thus False by (metis `n = defNode v` dom)
      qed
      hence "length (ns\<^sub>1@[?n\<^sub>0]) \<ge> 2" by (cases ns\<^sub>1, auto)
      with ns\<^sub>1 have 1: "n\<comment>ns\<^sub>1\<rightarrow>last ns\<^sub>1" "last ns\<^sub>1 \<in> set (predecessors ?n\<^sub>0)" by - (erule path2_unsnoc, simp, simp, erule path2_unsnoc, auto)
      from `v\<^sub>0 = chooseNext` v\<^sub>0 have triv: "isTrivialPhi v\<^sub>0 v" using substitution[of] by (auto simp:substNext_def)
      then obtain vs where vs: "phi v\<^sub>0 = Some vs" "set vs = {v\<^sub>0,v} \<or> set vs = {v}" by (auto simp:isTrivialPhi_def split:option.splits)
      hence[simp]: "var v\<^sub>0 = var v" by - (rule phiArg_same_var[symmetric], auto simp: phiArg_def)
      have[simp]: "v \<in> phiUses (last ns\<^sub>1)"
      proof-
        from vs ns\<^sub>1 1 have "v \<in> phiUses (last ns\<^sub>1) \<or> v\<^sub>0 \<in> phiUses (last ns\<^sub>1)" by - (rule phiUses_exI[of "last ns\<^sub>1" ?n\<^sub>0 v\<^sub>0 vs], auto simp:phi_def)
        moreover have "v\<^sub>0 \<notin> phiUses (last ns\<^sub>1)"
        proof
          assume asm: "v\<^sub>0 \<in> phiUses (last ns\<^sub>1)"
          from True have "last ns\<^sub>1 \<in> set ns\<^sub>1" by - (rule last_in_set, auto)
          hence "last ns\<^sub>1 \<in> set \<alpha>n" by - (rule path2_in_\<alpha>n[OF ns\<^sub>1(1)], auto)
          with asm ns\<^sub>1 have "dominates ?n\<^sub>0 (last ns\<^sub>1)" by - (rule allUses_dominated, auto)
          moreover have "strict_def_dom v v\<^sub>0" using triv by - (rule trivialPhi_strict_dom, auto)
          ultimately have "?n\<^sub>0 \<in> set ns\<^sub>1" using 1(1) by - (rule dominates_mid, auto)
          with ns\<^sub>1(2) show False ..
        qed
        ultimately show ?thesis by simp
      qed

      show ?thesis
      proof (cases "x \<in> set (tl ns\<^sub>1)")
        case True
        thus ?thesis using assms(2,3,6) by - (rule conventional[where x=x, OF 1(1)], auto simp:ns)
      next
        case False
        show ?thesis
        proof (cases "var v' = var v\<^sub>0")
          case [simp]: True
          {
            assume asm: "x \<in> set ns\<^sub>3"
            with assms(6)[THEN allDefs_narrows] have[simp]: "x = defNode v'"
              using ns\<^sub>3 by - (rule defNode_eq[symmetric], auto)
            {
              assume "v' = v\<^sub>0"
              hence False using assms(6) `v\<^sub>0 = chooseNext` simpleDefs_phiDefs_disjoint[of x] vs(1)
                by (auto simp: step.allDefs_def step.phiDefs_def)
            }
            moreover {
              assume "v' \<noteq> v\<^sub>0"
              hence "x \<noteq> ?n\<^sub>0" using allDefs_var_disjoint[OF _ assms(6)[THEN allDefs_narrows], of v\<^sub>0]
                by auto
              from ns\<^sub>3 asm ns obtain ns\<^sub>3 where ns\<^sub>3: "?n\<^sub>0\<comment>ns\<^sub>3\<rightarrow>?n\<^sub>0" "?n\<^sub>0 \<notin> set (tl (butlast ns\<^sub>3))" "x \<in> set ns\<^sub>3" "set ns\<^sub>3 \<subseteq> set (tl ns)"
                by - (rule path2_simple_loop, auto)
              with `x \<noteq> ?n\<^sub>0` have "length ns\<^sub>3 > 1"
                by (metis empty_iff graph_path_base.path2_def hd_Cons_tl insert_iff length_greater_0_conv length_tl list.set(1) list.set(2) zero_less_diff)
              with ns\<^sub>3 obtain ns' m where ns': "?n\<^sub>0\<comment>ns'\<rightarrow>m" "m \<in> set (predecessors ?n\<^sub>0)" "ns' = butlast ns\<^sub>3"
                by - (rule path2_unsnoc, auto)
              with vs ns\<^sub>3 have "v \<in> phiUses m \<or> v\<^sub>0 \<in> phiUses m"
                by - (rule phiUses_exI[of m ?n\<^sub>0 v\<^sub>0 vs], auto simp:phi_def)
              moreover {
                assume "v \<in> phiUses m"
                have "var v\<^sub>0 \<noteq> var v"
                proof (rule conventional)
                  show "n\<comment>ns\<^sub>1 @ ns'\<rightarrow>m" using path2_app'[OF ns\<^sub>1(1) ns'(1)] by simp
                  have "n \<notin> set (tl ns\<^sub>1)" using ns assms(2) by auto
                  moreover have "n \<notin> set ns'" using ns'(3) ns\<^sub>3(4) assms(2) by (auto dest: in_set_butlastD)
                  ultimately show "n \<notin> set (tl (ns\<^sub>1 @ ns'))" by simp
                  show "v \<in> allDefs n" using `v \<in> allDefs n` .
                  show "?n\<^sub>0 \<in> set (tl (ns\<^sub>1 @ ns'))" using ns'(1) by (auto simp: path2_def)
                qed (auto simp: `v \<in> phiUses m`)
                hence False by simp
              }
              moreover {
                assume "v\<^sub>0 \<in> phiUses m"
                moreover from ns\<^sub>3(1,3) `x \<noteq> ?n\<^sub>0` `length ns\<^sub>3 > 1` have "x \<in> set (tl (butlast ns\<^sub>3))"
                  by (cases ns\<^sub>3, auto simp: path2_def intro: in_set_butlastI)
                ultimately have "var v' \<noteq> var v\<^sub>0"
                  using assms(6)[THEN allDefs_narrows] ns\<^sub>3(2,3) ns'(3) by - (rule conventional[OF ns'(1)], auto)
                hence False by simp
              }
              ultimately have False by auto
            }
            ultimately have False by auto
          }
          moreover {
            assume asm: "x \<notin> set ns\<^sub>3"
            have "var v' \<noteq> var v\<^sub>0"
            proof (cases "x = ?n\<^sub>0")
              case True
              moreover have "v\<^sub>0 \<notin> step.allDefs ?n\<^sub>0" by (auto simp:`v\<^sub>0 = chooseNext` chooseNext_eliminated)
              ultimately show ?thesis using assms(6) vs(1) by - (rule allDefs_var_disjoint[of x], auto)
            next
              case False
              with `x \<notin> set (tl ns\<^sub>1)` assms(5) asm have "x \<in> set ns\<^sub>2" by (auto simp:ns)
              thus ?thesis using assms(2,6) v\<^sub>0(2) ns\<^sub>2(2) by - (rule conventional[OF ns\<^sub>2(1), where x=x], auto simp:ns)
            qed
          }
          ultimately show ?thesis by auto
        qed auto
      qed
    qed
  qed

  lemma[simp]: "var (substNext v) = var v"
    using substitution[OF redundant]
    by (auto simp:substNext_def isTrivialPhi_def phi_def split:option.splits)

  lemma phis_same_var_inv:
    assumes "phis' (n,v) = Some vs" "v' \<in> set vs"
    shows "var v' = var v"
  proof-
    from assms obtain vs\<^sub>0 v\<^sub>0 where 1: "phis (n,v) = Some vs\<^sub>0" "v\<^sub>0 \<in> set vs\<^sub>0" "v' = substNext v\<^sub>0" by (auto split:split_if_asm)
    hence "var v\<^sub>0 = var v" by auto
    with 1 show ?thesis by auto
  qed

  lemma allDefs_var_disjoint_inv: "\<lbrakk>n \<in> set \<alpha>n; v \<in> step.allDefs n; v' \<in> step.allDefs n; v \<noteq> v'\<rbrakk> \<Longrightarrow> var v' \<noteq> var v"
    using allDefs_var_disjoint
    by (auto simp:step.allDefs_def)

  lemma step_CFG_SSA_Transformed_notriv: "CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses defs uses' phis' var chooseNext_all"
  apply unfold_locales
       apply (rule oldDefs_def)
      apply (simp add:oldUses_inv)
     apply (simp add:conventional_inv)
    apply (simp add:phis_same_var_inv)
   apply (simp add:allDefs_var_disjoint_inv)
  by (rule chooseNext_all)

  sublocale step: CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses "defs" uses' phis' var chooseNext_all
  by (rule step_CFG_SSA_Transformed_notriv)

  lemma step_defNode: "v \<in> allVars \<Longrightarrow> v \<noteq> chooseNext \<Longrightarrow> step.defNode v = defNode v"
  by (auto simp: step.CFG_SSA_wf_defs dom_def CFG_SSA_wf_defs)

  lemma step_phi: "v \<in> allVars \<Longrightarrow> v \<noteq> chooseNext \<Longrightarrow> step.phi v = map_option (map (substNext)) (phi v)"
  by (auto simp: step.phi_def step_defNode phi_def)

  lemma liveVal'_inv:
    assumes "liveVal' (v#vs)" "v \<noteq> chooseNext"
    obtains vs' where "step.liveVal' (v#vs')"
  using assms proof (induction "length vs" arbitrary: v vs rule: nat_less_induct)
    case (1 vs v)
    from "1.prems"(2) show thesis
    proof cases
      case (liveSimple' n)
      with "1.prems"(3) show thesis by - (rule "1.prems"(1), rule step.liveSimple', auto simp: substNext_def)
    next
      case (livePhi' v' vs')
      from this(2) have[simp]: "v' \<in> allVars" by - (drule liveVal'D, rule, rule liveVal_in_allVars)
      show thesis
      proof (cases "chooseNext = v'")
        case False
        show thesis
        proof (rule "1.hyps"[rule_format, of "length vs'" vs' v'])
          fix vs'\<^sub>2
          assume asm: "step.liveVal' (v'#vs'\<^sub>2)"
          have "step.phiArg v' v" using livePhi'(3) False "1.prems"(3) by (auto simp: step.phiArg_def phiArg_def step_phi substNext_def)
          thus thesis by - (rule "1.prems"(1), rule step.livePhi', rule asm)
        qed (auto simp: livePhi' False[symmetric])
      next
        case[simp]: True
        with "1.prems"(3) have[simp]: "v \<noteq> v'" by simp
        from True have "trivial v'" using chooseNext[OF redundant] by auto
        with `phiArg v' v` have "isTrivialPhi v' v" by (auto simp: phiArg_def trivial_def isTrivialPhi_def)
        hence[simp]: "substitution = v" unfolding substitution_def
        by - (rule the1_equality, auto intro!: isTrivialPhi_det[unfolded trivial_def])

        obtain vs'\<^sub>2 where vs'\<^sub>2: "suffixeq (v'#vs'\<^sub>2) (v'#vs')" "v' \<notin> set vs'\<^sub>2"
          using split_list_last[of v' "v'#vs'"] by (auto simp: suffixeq_def)
        with `liveVal' (v'#vs')` have "liveVal' (v'#vs'\<^sub>2)" by - (rule liveVal'_suffixeq, simp_all)
        thus thesis
        proof (cases rule: liveVal'.cases)
          case (liveSimple' n)
          hence "v \<in> uses' n" by (auto simp: substNext_def)
          with liveSimple' show thesis by - (rule "1.prems"(1), rule step.liveSimple', auto)
        next
          case (livePhi' v'' vs'')
          from this(2) have[simp]: "v'' \<in> allVars" by - (drule liveVal'D, rule, rule liveVal_in_allVars)
          from vs'\<^sub>2(2) livePhi'(1) have[simp]: "v'' \<noteq> v'" by auto
          show thesis
          proof (rule "1.hyps"[rule_format, of "length vs''" vs'' v''])
            show "length vs'' < length vs" using `vs = v'#vs'` livePhi'(1) vs'\<^sub>2(1)[THEN suffixeq_ConsD2]
              by (auto simp: suffixeq_def)
          next
            fix vs''\<^sub>2
            assume asm: "step.liveVal' (v''#vs''\<^sub>2)"
            from livePhi' `phiArg v' v` have "step.phiArg v'' v" by (auto simp: phiArg_def step.phiArg_def step_phi substNext_def)
            thus thesis by - (rule "1.prems"(1), rule step.livePhi', rule asm)
          qed (auto simp: livePhi'(2))
        qed
      qed
    qed
  qed

  lemma liveVal_inv:
    assumes "liveVal v" "v \<noteq> chooseNext"
    shows "step.liveVal v"
  apply (rule liveVal'I[OF assms(1)])
  apply (erule liveVal'_inv[OF _ assms(2)])
  apply (rule step.liveVal'D)
  by simp_all

  lemma pruned_inv:
    assumes "pruned"
    shows "step.pruned"
  proof (rule step.pruned_def[THEN iffD2, rule_format])
    fix n v
    assume "v \<in> step.phiDefs n" and[simp]: "n \<in> set \<alpha>n"
    hence "v \<in> phiDefs n" "v \<noteq> chooseNext" by (auto simp: step.CFG_SSA_defs CFG_SSA_defs split: split_if_asm)
    hence "liveVal v" using assms by (auto simp: pruned_def)
    thus "step.liveVal v" using `v \<noteq> chooseNext` by (rule liveVal_inv)
  qed
end

context CFG_SSA_Transformed_notriv_base
begin
  abbreviation "inst u p \<equiv> CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses defs u p var chooseNext_all"
  abbreviation "inst' \<equiv> \<lambda>(u,p). inst u p"

  interpretation uninst: CFG_SSA_Transformed_notriv_base \<alpha>n predecessors Entry oldDefs oldUses "defs" u p var chooseNext_all
  for u and p
  by unfold_locales

  definition "cond \<equiv> \<lambda>(u,p). uninst.redundant u p"
  definition "step \<equiv> \<lambda>(u,p). (uninst.uses' u p, uninst.phis' u p)"
  definition[code]: "substAll \<equiv> while (cond) (step) (uses,phis)"

  definition[code]: "uses'_all \<equiv> fst (substAll)"
  definition[code]: "phis'_all \<equiv> snd (substAll)"
end

context CFG_SSA_Transformed_notriv
begin
  declare fun_upd_apply[simp del] fun_upd_same[simp]

  lemma substAll_wf:
    assumes[simp]: "redundant"
    shows "card (dom (phis')) < card (dom phis)"
  proof (rule psubset_card_mono)
    let ?v = "chooseNext"
    from chooseNext[of] obtain n where "(n,?v) \<in> dom phis" by (auto simp: trivial_def isTrivialPhi_def phi_def split:option.splits)
    moreover have "(n,?v) \<notin> dom (phis')" by auto
    ultimately have "dom (phis') \<noteq> dom phis" by auto
    thus "dom (phis') \<subset> dom phis" by (auto split:split_if_asm)
  qed (rule phis_finite)

  lemma step_preserves_inst:
    assumes "inst' (u,p)"
      and "CFG_SSA_wf_base.redundant \<alpha>n predecessors defs u p"
    shows "inst' (step (u,p))"
  proof-
    from assms(1) interpret i: CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses "defs" u p var
    by simp

    from assms(2) interpret step: CFG_SSA_step \<alpha>n predecessors Entry oldDefs oldUses "defs" u p var chooseNext_all
    by unfold_locales

    show ?thesis using step.step_CFG_SSA_Transformed_notriv[simplified] by (simp add: step_def)
  qed

  lemma substAll:
    assumes "P (uses, phis)"
    assumes "\<And>x. P x \<Longrightarrow> inst' x \<Longrightarrow> cond x \<Longrightarrow> P (step x)"
    assumes "\<And>x. P x \<Longrightarrow> inst' x \<Longrightarrow> \<not>cond x \<Longrightarrow> Q (fst x) (snd x)"
    shows "inst (uses'_all) (phis'_all)" "Q (uses'_all) (phis'_all)"
  proof-
    note uses'_def[simp del]
    note phis'_def[simp del]
    have 2: "\<And>f x. f x = f (fst x, snd x)" by simp

    have "inst' (substAll) \<and> Q (uses'_all) (phis'_all)" unfolding substAll_def uses'_all_def phis'_all_def
    apply (rule while_rule[where P="\<lambda>x. inst' x \<and> P x"])
        apply (rule conjI)
         apply (simp, unfold_locales)
        apply (rule assms(1))
       apply (rule conjI)
        apply (clarsimp simp: cond_def step_def)
        apply (rule step_preserves_inst [unfolded step_def, simplified], assumption+)
       proof-
         show "wf {(y,x). (inst' x \<and> cond x) \<and> y = step x}"
         apply (rule wf_if_measure[where f="\<lambda>(u,p). card (dom p)"])
         apply (clarsimp simp: cond_def step_def split:prod.split)
         proof-
           fix u p
           assume "inst u p"
           then interpret i: CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses "defs" u p by simp
           assume "i.redundant"
           thus "card (dom (i.phis')) < card (dom p)" by (rule i.substAll_wf[of, simplified])
         qed
       qed (auto intro: assms(2,3))
    thus "inst (uses'_all) (phis'_all)" "Q (uses'_all) (phis'_all)"
    by (auto simp: uses'_all_def phis'_all_def)
  qed

  sublocale notriv: CFG_SSA_Transformed \<alpha>n predecessors Entry oldDefs oldUses "defs" uses'_all phis'_all var
  by (cut_tac substAll, auto simp: CFG_SSA_Transformed_notriv_def)

  theorem not_redundant: "\<not>notriv.redundant"
  by (rule substAll(2)[where Q="\<lambda>u p. \<not>CFG_SSA_wf_base.redundant \<alpha>n predecessors defs u p" and P="\<lambda>_. True", simplified cond_def substAll_def], auto)

  corollary minimal: "reducible \<Longrightarrow> notriv.cytronMinimal"
  by (erule notriv.reducible_nonredundant_imp_minimal, rule not_redundant)

  theorem pruned_invariant:
    assumes "pruned"
    shows "notriv.pruned"
  proof-
    {
      fix u p
      assume "inst u p"
      then interpret i: CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses "defs" u p var chooseNext_all
      by simp

      assume "i.redundant"
      then interpret i: CFG_SSA_step \<alpha>n predecessors Entry oldDefs oldUses "defs" u p var chooseNext_all
      by unfold_locales

      interpret uninst: CFG_SSA_Transformed_notriv_base \<alpha>n predecessors Entry oldDefs oldUses "defs" u p var chooseNext_all
      for u and p
      by unfold_locales

      assume "i.pruned"
      hence "uninst.pruned i.uses' i.phis'"
        by (rule i.pruned_inv)
    }
    note 1 = this

    interpret uninst: CFG_SSA_Transformed_notriv_base \<alpha>n predecessors Entry oldDefs oldUses "defs" u p var chooseNext_all
    for u and p
    by unfold_locales

    from 1 assms show ?thesis
    by - (rule substAll(2)[where P="\<lambda>(u,p). uninst.pruned u p" and Q="uninst.pruned"],
          auto simp: cond_def step_def)
  qed
end

end
