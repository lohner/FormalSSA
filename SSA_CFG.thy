(*  Title:      SSA_CFG.thy
    Author:     Sebastian Ullrich, Denis Lohner
*)

theory SSA_CFG
imports Main Relation Graph_path "~~/src/HOL/Library/Sublist"
begin

subsection {* CFG *}

locale CFG_base = graph_Entry_base \<alpha>n predecessors Entry
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry :: "'node" +
fixes "defs" :: "'node \<Rightarrow> 'var::linorder set"
fixes "uses" :: "'node \<Rightarrow> 'var set"
begin
  definition "vars \<equiv> fold (op \<union>) (map uses \<alpha>n) {}"
  definition defAss' :: "'node \<Rightarrow> 'var \<Rightarrow> bool" where
    "defAss' m v \<longleftrightarrow> (\<forall>ns. Entry\<comment>ns\<rightarrow>m \<longrightarrow> (\<exists>n \<in> set ns. v \<in> defs n))"
  definition defAss'Uses :: bool where
    "defAss'Uses \<equiv> \<forall>m \<in> set \<alpha>n. \<forall>v \<in> uses m. defAss' m v"
end

locale CFG = CFG_base \<alpha>n predecessors Entry "defs" "uses"
+ graph_Entry \<alpha>n predecessors Entry
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry :: "'node" and
  "defs" :: "'node \<Rightarrow> 'var::linorder set" and
  "uses" :: "'node \<Rightarrow> 'var set" +
assumes defs_uses_disjoint: "n \<in> set \<alpha>n \<Longrightarrow> defs n \<inter> uses n = {}"
assumes defs_finite[simp]: "finite (defs n)"
assumes uses_in_\<alpha>n: "v \<in> uses n \<Longrightarrow> n \<in> set \<alpha>n"
assumes uses_finite[simp, intro!]: "finite (uses n)"
begin
  lemma vars_finite[simp]: "finite (vars)"
  by (auto simp:vars_def)

  lemma uses_in_vars[elim, simp]: "v \<in> uses n \<Longrightarrow>  v \<in> vars"
  by (auto simp add:vars_def uses_in_\<alpha>n intro!: fold_union_elemI)

  lemma varsE:
    assumes "v \<in> vars"
    obtains n where "n \<in> set \<alpha>n" "v \<in> uses n"
  using assms by (auto simp:vars_def elim!:fold_union_elem)

  lemma defs_uses_disjoint'[simp]: "n \<in> set \<alpha>n \<Longrightarrow> v \<in> defs n \<Longrightarrow> v \<in> uses n \<Longrightarrow> False"
  using defs_uses_disjoint by auto
end

context CFG
begin
  lemma defAss'E:
    assumes "defAss' m v" "Entry\<comment>ns\<rightarrow>m"
    obtains n where "n \<in> set ns" "v \<in> defs n"
  using assms unfolding defAss'_def by auto

  lemmas defAss'I = defAss'_def[THEN iffD2, rule_format]

  lemma defAss'_extend:
    assumes "defAss' m v"
    assumes "n\<comment>ns\<rightarrow>m" "\<forall>n \<in> set (tl ns). v \<notin> defs n"
    shows "defAss' n v"
  unfolding defAss'_def proof (rule allI, rule impI)
    fix ns'
    assume "Entry\<comment>ns'\<rightarrow>n"
    with assms(2) have "Entry\<comment>ns'@tl ns\<rightarrow>m" by auto
    with assms(1) obtain n' where n': "n' \<in> set (ns'@tl ns)" "v \<in> defs n'" by -(erule defAss'E)
    with assms(3) have "n' \<notin> set (tl ns)" by auto
    with n' show "\<exists>n \<in> set ns'. v \<in> defs n" by auto
  qed
end

text {* A CFG is well-formed if it satisfies definite assignment. *}

locale CFG_wf = CFG \<alpha>n predecessors Entry "defs" "uses"
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  "defs" :: "'node \<Rightarrow> 'var::linorder set" and
  "uses" :: "'node \<Rightarrow> 'var set" +
assumes def_ass_uses: "\<forall>m \<in> set \<alpha>n. \<forall>v \<in> uses m. defAss' m v"

subsection {* SSA CFG *}

type_synonym ('node, 'val) phis = "'node \<times> 'val \<rightharpoonup> 'val list"

declare in_set_zipE[elim]
declare zip_same[simp]

locale CFG_SSA_base = CFG_base \<alpha>n predecessors Entry "defs" "uses"
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'node \<Rightarrow> 'val set" +
fixes phis :: " ('node, 'val) phis"
begin
  definition "phiDefs n \<equiv> {v. (n,v) \<in> dom phis}"
  definition[code]: "allDefs n \<equiv> defs n \<union> phiDefs n"

  definition[code]: "phiUses n \<equiv>
    \<Union>n' \<in> set (successors n). \<Union>v' \<in> phiDefs n'. snd ` Set.filter (\<lambda>(n'',v). n'' = n) (set (zip (predecessors n') (the (phis (n',v')))))"
  definition[code]: "allUses n \<equiv> uses n \<union> phiUses n"
  definition[code]: "allVars \<equiv> \<Union>n \<in> set \<alpha>n. allDefs n \<union> allUses n"

  definition defAss :: "'node \<Rightarrow> 'val \<Rightarrow> bool" where
    "defAss m v \<longleftrightarrow> (\<forall>ns. Entry\<comment>ns\<rightarrow>m \<longrightarrow> (\<exists>n \<in> set ns. v \<in> allDefs n))"

  lemmas CFG_SSA_defs = phiDefs_def allDefs_def phiUses_def allUses_def allVars_def defAss_def
end

locale CFG_SSA = CFG \<alpha>n predecessors Entry "defs" "uses" + CFG_SSA_base \<alpha>n predecessors Entry "defs" "uses" phis
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'node \<Rightarrow> 'val set" and
   phis :: " ('node, 'val) phis" +
assumes phis_finite: "finite (dom phis)"
assumes phis_in_\<alpha>n: "phis (n,v) = Some vs \<Longrightarrow> n \<in> set \<alpha>n"
assumes phis_wf:
  "phis (n,v) = Some args \<Longrightarrow> length (predecessors n) = length args"
assumes simpleDefs_phiDefs_disjoint:
  "n \<in> set \<alpha>n \<Longrightarrow> defs n \<inter> phiDefs n = {}"
assumes allDefs_disjoint:
  "\<lbrakk>n \<in> set \<alpha>n; m \<in> set \<alpha>n; n \<noteq> m\<rbrakk> \<Longrightarrow> allDefs n \<inter> allDefs m = {}"
begin
  lemma phis_disj:
    assumes "phis (n,v) = Some vs"
    and "phis (n',v) = Some vs'"
    shows "n = n'" and "vs = vs'"
  proof -
    from assms have "n \<in> set \<alpha>n" and "n' \<in> set \<alpha>n"
      by (auto dest: phis_in_\<alpha>n)
    from allDefs_disjoint [OF this] assms show "n = n'"
      by (auto simp: allDefs_def phiDefs_def)
    with assms show "vs = vs'" by simp
  qed

  lemma allDefs_disjoint': "\<lbrakk>n \<in> set \<alpha>n; m \<in> set \<alpha>n; v \<in> allDefs n; v \<in> allDefs m\<rbrakk> \<Longrightarrow> n = m"
  using allDefs_disjoint by auto

  lemma phiUsesI:
    assumes "n' \<in> set \<alpha>n" "phis (n',v') = Some vs" "(n,v) \<in> set (zip (predecessors n') vs)"
    shows "v \<in> phiUses n"
  proof-
    from assms(3) have "n \<in> set (predecessors n')" by auto
    hence 1: "n' \<in> set (successors n)" using assms(1) by simp
    from assms(2) have 2: "v' \<in> phiDefs n'" by (auto simp add:phiDefs_def)
    from assms(2) have 3: "the (phis (n',v')) = vs" by simp
    show ?thesis unfolding phiUses_def by (rule UN_I[OF 1], rule UN_I[OF 2], auto simp:image_def Set.filter_def assms(3) 3)
  qed

  lemma phiUsesE:
    assumes "v \<in> phiUses n"
    obtains  n' v' vs where "n' \<in> set (successors n)" "(n,v) \<in> set (zip (predecessors n') vs)" "phis (n', v') = Some vs"
  proof-
    from assms(1) obtain n' v' where "n'\<in>set (successors n)" "v'\<in>phiDefs n'"
      "v \<in> snd ` Set.filter (\<lambda>(n'', v). n'' = n) (set (zip (predecessors n') (the (phis (n', v')))))" by (auto simp:phiUses_def)
    thus ?thesis by - (rule that[of n' "the (phis (n',v'))" v'], auto simp:phiDefs_def)
  qed

  lemma defs_in_allDefs[intro]: "v \<in> defs n \<Longrightarrow> v \<in> allDefs n" by (simp add:allDefs_def)
  lemma phiDefs_in_allDefs[intro]: "v \<in> phiDefs n \<Longrightarrow> v \<in> allDefs n" by (simp add:allDefs_def)
  lemma uses_in_allUses[intro]: "v \<in> uses n \<Longrightarrow> v \<in> allUses n" by (simp add:allUses_def)
  lemma phiUses_in_allUses[simp]: "v \<in> phiUses n \<Longrightarrow> v \<in> allUses n" by (simp add:allUses_def)
  lemma allDefs_in_allVars[intro]: "\<lbrakk>v \<in> allDefs n; n \<in> set \<alpha>n\<rbrakk> \<Longrightarrow> v \<in> allVars" by (auto simp:allVars_def)
  lemma allUses_in_allVars[intro]: "\<lbrakk>v \<in> allUses n; n \<in> set \<alpha>n\<rbrakk> \<Longrightarrow> v \<in> allVars" by (auto simp:allVars_def)

  lemma phiDefs_finite[simp]: "finite (phiDefs n)"
  unfolding phiDefs_def
  proof (rule finite_surj[where f=snd], rule phis_finite)
    have "\<And>x y. phis (n,x) = Some y \<Longrightarrow> x \<in> snd ` dom phis" by (metis domI imageI snd_conv)
    thus "{v. (n, v) \<in> dom phis} \<subseteq> snd ` dom phis" by auto
  qed

  lemma phiUses_finite[simp]:
    assumes "n \<in> set \<alpha>n"
    shows "finite (phiUses n)"
  by (auto simp:phiUses_def Set.filter_def)

  lemma allDefs_finite[intro!]: "n \<in> set \<alpha>n \<Longrightarrow> finite (allDefs n)" by (auto simp add:allDefs_def)
  lemma allUses_finite[intro!]: "n \<in> set \<alpha>n \<Longrightarrow> finite (allUses n)" by (auto simp add:allUses_def)
  lemma allVars_finite[simp]: "finite (allVars)" by (auto simp add:allVars_def)

  lemmas defAssI = defAss_def[THEN iffD2, rule_format]
  lemmas defAssD = defAss_def[THEN iffD1, rule_format]

  lemma defAss_extend:
    assumes "defAss m v"
    assumes "n\<comment>ns\<rightarrow>m" "\<forall>n \<in> set (tl ns). v \<notin> allDefs n"
    shows "defAss n v"
  unfolding defAss_def proof (rule allI, rule impI)
    fix ns'
    assume "Entry\<comment>ns'\<rightarrow>n"
    with assms(2) have "Entry\<comment>ns'@tl ns\<rightarrow>m" by auto
    with assms(1) obtain n' where n': "n' \<in> set (ns'@tl ns)" "v \<in> allDefs n'" by (auto dest:defAssD)
    with assms(3) have "n' \<notin> set (tl ns)" by auto
    with n' show "\<exists>n \<in> set ns'. v \<in> allDefs n" by auto
  qed

  lemma defAss_dominating:
    assumes[simp]: "n \<in> set \<alpha>n"
    shows "defAss n v \<longleftrightarrow> (\<exists>m \<in> set \<alpha>n. dominates m n \<and> v \<in> allDefs m)"
  proof
    assume asm: "defAss n v"
    obtain ns where ns: "Entry\<comment>ns\<rightarrow>n" by (atomize, auto)
    from defAssD[OF asm this] obtain m where m: "m \<in> set ns" "v \<in> allDefs m" by auto
    have "dominates m n"
    proof (rule dominatesI)
      fix ns'
      assume ns': "Entry\<comment>ns'\<rightarrow>n"
      from defAssD[OF asm this] obtain m' where m': "m' \<in> set ns'" "v \<in> allDefs m'" by auto
      with m ns ns' have "m' = m" by - (rule allDefs_disjoint', auto)
      with m' show "m \<in> set ns'" by simp
    qed simp
    with m ns show "\<exists>m\<in>set \<alpha>n. dominates m n \<and> v \<in> allDefs m" by auto
  next
    assume "\<exists>m \<in> set \<alpha>n. dominates m n \<and> v \<in> allDefs m"
    then obtain m where[simp]: "m \<in> set \<alpha>n" and m: "dominates m n" "v \<in> allDefs m" by auto
    show "defAss n v"
    proof (rule defAssI)
      fix ns
      assume "Entry\<comment>ns\<rightarrow>n"
      with m(1) have "m \<in> set ns" by - (rule dominates_mid, auto)
      with m(2) show "\<exists>n\<in>set ns. v \<in> allDefs n" by auto
    qed
  qed
end

locale CFG_SSA_wf_base = CFG_SSA_base \<alpha>n predecessors Entry "defs" "uses" phis
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'node \<Rightarrow> 'val set" and
  phis :: " ('node, 'val) phis"
begin
  text {* Using the SSA properties, we can map every value to its unique defining node and
    remove the @{typ 'node} parameter of the @{term phis} map. *}

  definition defNode :: "'val \<Rightarrow> 'node" where
    defNode_code [code]: "defNode v \<equiv> hd [n \<leftarrow> \<alpha>n. v \<in> allDefs n]"

  abbreviation "def_dominates v' v \<equiv> dominates (defNode v') (defNode v)"
  abbreviation "strict_def_dom v' v \<equiv> defNode v' \<noteq> defNode v \<and> def_dominates v' v"

  definition "phi v = phis (defNode v,v)"
  definition[simp]: "phiArg v v' \<equiv> \<exists>vs. phi v = Some vs \<and> v' \<in> set vs"

  definition[code]: "isTrivialPhi v v' \<longleftrightarrow> v' \<noteq> v \<and>
    (case phi v of
      Some vs \<Rightarrow> set vs = {v,v'} \<or> set vs = {v'}
    | None \<Rightarrow> False)"
  definition[code]: "trivial v \<equiv> \<exists>v' \<in> allVars. isTrivialPhi v v'"
  definition[code]: "redundant \<equiv> \<exists>v \<in> allVars. trivial v"

  definition "defAssUses \<equiv> \<forall>n \<in> set \<alpha>n. \<forall>v \<in> allUses n. defAss n v"

  declare [[inductive_internals]]
  inductive liveVal :: "'val \<Rightarrow> bool"
  where
    liveSimple: "\<lbrakk>n \<in> set \<alpha>n; val \<in> uses n\<rbrakk> \<Longrightarrow> liveVal val"
  | livePhi: "\<lbrakk>liveVal v; phiArg v v'\<rbrakk> \<Longrightarrow> liveVal v'"

  definition "pruned = (\<forall>n \<in> set \<alpha>n. \<forall>val. val \<in> phiDefs n \<longrightarrow> liveVal val)"

  lemmas "CFG_SSA_wf_defs" = CFG_SSA_defs defNode_code phi_def isTrivialPhi_def trivial_def redundant_def liveVal_def pruned_def
end

locale CFG_SSA_wf = CFG_SSA \<alpha>n predecessors Entry "defs" "uses" phis
  + CFG_SSA_wf_base \<alpha>n predecessors Entry "defs" "uses" phis
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'node \<Rightarrow> 'val set" and
  phis :: " ('node, 'val) phis" +
  assumes allUses_def_ass: "\<lbrakk>v \<in> allUses n; n \<in> set \<alpha>n\<rbrakk> \<Longrightarrow> defAss n v"
  assumes Entry_no_phis[simp]: "phis (Entry,v) = None"
begin
  lemma allVars_in_allDefs: "v \<in> allVars \<Longrightarrow> \<exists>n \<in> set \<alpha>n. v \<in> allDefs n"
    unfolding allVars_def
  apply auto
  apply (drule(1) allUses_def_ass)
  apply (clarsimp simp: defAss_def)
  apply (drule Entry_reaches)
   apply auto[1]
  by fastforce

  lemma phiDefs_Entry_empty[simp]: "phiDefs (Entry) = {}"
  by (auto simp: phiDefs_def)

  lemma phi_Entry_empty[simp]: "defNode v = Entry \<Longrightarrow> phi v = None"
    by (simp add:phi_def)

  lemma defNode_ex1:
    assumes "v \<in> allVars"
    shows "\<exists>!n. n \<in> set \<alpha>n \<and> v \<in> allDefs n"
  proof (rule ex_ex1I)
    show "\<exists>n. n \<in> set \<alpha>n \<and> v \<in> allDefs n"
    proof-
      from assms(1) obtain n where n: "n \<in> set \<alpha>n" "v \<in> allDefs n \<or> v \<in> allUses n" by (auto simp:allVars_def)
      thus ?thesis
      proof (cases "v \<in> allUses n")
        case True
        from n(1) obtain ns where ns: "Entry\<comment>ns\<rightarrow>n" by (atomize_elim, rule Entry_reaches)
        with allUses_def_ass[OF True n(1)] obtain m where m: "m \<in> set ns" "v \<in> allDefs m" by - (drule defAssD, auto)
        from ns this(1) have "m \<in> set \<alpha>n" by (rule path2_in_\<alpha>n)
        with n(1) m show ?thesis by auto
      qed auto
    qed
    show "\<And>n m. n \<in> set \<alpha>n \<and> v \<in> allDefs n \<Longrightarrow> m \<in> set \<alpha>n \<and> v \<in> allDefs m \<Longrightarrow> n = m" using allDefs_disjoint by auto
  qed

  lemma defNode_def: "v \<in> allVars \<Longrightarrow> defNode v = (THE n. n \<in> set \<alpha>n \<and> v \<in> allDefs n)"
  unfolding defNode_code by (rule the1_list[symmetric], rule defNode_ex1)

  lemma defNode[simp]:
    assumes "v \<in> allVars"
    shows  "(defNode v) \<in> set \<alpha>n" "v \<in> allDefs (defNode v)"
  apply (atomize(full))
  unfolding defNode_def[OF assms] using assms
  by - (rule theI', rule defNode_ex1)

  lemma defNode_eq[intro]:
    assumes "n \<in> set \<alpha>n" "v \<in> allDefs n"
    shows "defNode v = n"
  apply (subst defNode_def, rule allDefs_in_allVars[OF assms(2) assms(1)])
  by (rule the1_equality, rule defNode_ex1, rule allDefs_in_allVars[where n=n], simp_all add:assms)

  lemma defNode_cases[consumes 1]:
    assumes "v \<in> allVars"
    obtains (simpleDef) "v \<in> defs (defNode v)"
          | (phi)       "phi v \<noteq> None"
  proof (cases "v \<in> defs (defNode v)")
    case True
    thus thesis by (rule simpleDef)
  next
    case False
    with assms[THEN defNode(2)] show thesis
      by - (rule phi, auto simp: allDefs_def phiDefs_def phi_def)
  qed

  lemma phi_phiDefs[simp]: "phi v = Some vs \<Longrightarrow> v \<in> phiDefs (defNode v)" by (auto simp:phiDefs_def phi_def)

  lemma simpleDef_not_phi:
    assumes "n \<in> set \<alpha>n" "v \<in> defs n"
    shows "phi v = None"
  proof-
    from assms have "defNode v = n" by auto
    with assms show ?thesis using simpleDefs_phiDefs_disjoint by (auto simp: phi_def phiDefs_def)
  qed

  lemma phi_wf: "phi v = Some vs \<Longrightarrow> length (predecessors (defNode v)) = length vs"
  by (rule phis_wf) (simp add:phi_def)

  lemma phi_finite: "finite (dom (phi))"
  proof-
    let ?f = "\<lambda>v. (defNode v,v)"
    have "phi = phis \<circ> ?f" by (auto simp add:phi_def)
    moreover have "inj ?f" by (auto intro:injI)
    hence "finite (dom (phis \<circ> ?f))" by - (rule finite_dom_comp, auto simp add:phis_finite inj_on_def)
    ultimately show ?thesis by simp
  qed

  lemma phiUses_exI:
    assumes "m \<in> set (predecessors n)" "phis (n,v) = Some vs" "n \<in> set \<alpha>n"
    obtains v' where "v' \<in> phiUses m" "v' \<in> set vs"
  proof-
    from assms(1) obtain i where i: "m = predecessors n ! i" "i < length (predecessors n)" by (metis in_set_conv_nth)
    with assms(2) phis_wf have[simp]: "i < length vs" by (auto simp add:phi_def)
    from i assms(2,3) have "vs ! i \<in> phiUses m" by - (rule phiUsesI, auto simp add:phiUses_def phi_def set_zip)
    thus thesis by (rule that) (auto simp add:i(2) phis_wf)
  qed

  lemma phiArg_exI:
    assumes "m \<in> set (predecessors (defNode v))" "phi v \<noteq> None" and[simp]: "v \<in> allVars"
    obtains v' where "v' \<in> phiUses m" "phiArg v v'"
  proof-
    from assms(2) obtain vs where "phi v = Some vs" by auto
    with assms(1) show thesis
      by - (rule phiUses_exI, auto intro!:that simp: phi_def)
  qed

  lemma phiUses_exI':
    assumes "phiArg p q" and[simp]: "p \<in> allVars"
    obtains m where "q \<in> phiUses m" "m \<in> set (predecessors (defNode p))"
  proof-
    let ?n = "defNode p"
    from assms(1) obtain i vs where vs: "phi p = Some vs" and i: "q = vs ! i" "i < length vs" by (metis in_set_conv_nth phiArg_def)
    with phis_wf have[simp]: "i < length (predecessors ?n)" by (auto simp add:phi_def)
    from vs i have "q \<in> phiUses (predecessors ?n ! i)" by - (rule phiUsesI, auto simp add:phiUses_def phi_def set_zip)
    thus thesis by (rule that) (auto simp add:i(2) phis_wf)
  qed

  lemma phiArg_in_allVars[simp]:
    assumes "phiArg v v'"
    shows "v' \<in> allVars"
  proof-
    let ?n = "defNode v"
    from assms(1) obtain vs where vs: "phi v = Some vs" "v' \<in> set vs" by auto
    then obtain m where m: "(m,v') \<in> set (zip (predecessors ?n) vs)" by - (rule set_zip_leftI, rule phi_wf)
    from vs(1) have n: "?n \<in> set \<alpha>n" by (simp add: phi_def phis_in_\<alpha>n)
    with m have[simp]: "m \<in> set \<alpha>n" by auto
    from n m vs have "v' \<in> phiUses m" by - (rule phiUsesI, simp_all add:phi_def)
    thus ?thesis by - (rule allUses_in_allVars, auto simp:allUses_def)
  qed

  lemma defAss_defNode:
    assumes "defAss m v" "v \<in> allVars" "Entry\<comment>ns\<rightarrow>m"
    shows "defNode v \<in> set ns"
  proof-
    from assms obtain n where n: "n \<in> set ns" "v \<in> allDefs n" by (auto simp:defAss_def)
    with assms(3) have "n = defNode v" by - (rule defNode_eq[symmetric], auto)
    with n show "defNode v \<in> set ns" by (simp add:defAss_def)
  qed

  lemma defUse_path_ex:
    assumes "v \<in> allUses m" "m \<in> set \<alpha>n"
    obtains ns where "defNode v\<comment>ns\<rightarrow>m" "EntryPath ns"
  proof-
    from assms have "defAss m v" by - (rule allUses_def_ass, auto)
    moreover from assms obtain ns where ns: "Entry\<comment>ns\<rightarrow>m" "EntryPath ns"
      by - (atomize_elim, rule Entry_reachesE, auto)
    ultimately have "defNode v \<in> set ns" using assms(1)
      by - (rule defAss_defNode, auto)
    with ns(1) obtain ns' where "defNode v\<comment>ns'\<rightarrow>m" "suffixeq ns' ns"
      by (rule path2_split_ex', auto simp: suffixeq_def)
    thus thesis using ns(2)
      by - (rule that, assumption, rule EntryPath_suffixeq, auto)
  qed

  lemma defUse_path_dominated:
    assumes "defNode v\<comment>ns\<rightarrow>n" "defNode v \<notin> set (tl ns)" "v \<in> allUses n" "n' \<in> set ns"
    shows "dominates (defNode v) n'"
  proof (rule dominatesI)
    fix es
    assume asm: "Entry\<comment>es\<rightarrow>n'"
    from assms(1,4) obtain ns' where ns': "n'\<comment>ns'\<rightarrow>n" "suffixeq ns' ns"
      by - (rule path2_split_ex, auto simp: suffixeq_def)
    from assms have "defAss n v" by - (rule allUses_def_ass, auto)
    with asm ns'(1) assms(3) have "defNode v \<in> set (es@tl ns')" by - (rule defAss_defNode, auto)
    with suffixeq_tl_subset[OF ns'(2)] assms(2) show "defNode v \<in> set es" by auto
  next
    show "n' \<in> set \<alpha>n" using assms(1,4) by auto
  qed

  lemma allUses_dominated:
    assumes "v \<in> allUses n" "n \<in> set \<alpha>n"
    shows "dominates (defNode v) n"
  proof-
    from assms obtain ns where "defNode v\<comment>ns\<rightarrow>n" "defNode v \<notin> set (tl ns)"
      by - (rule defUse_path_ex, auto elim: simple_path2)
    with assms(1) show ?thesis by - (rule defUse_path_dominated, auto)
  qed

  lemma phiArg_path_ex':
    assumes "phiArg p q" and[simp]: "p \<in> allVars"
    obtains ns m where "defNode q\<comment>ns\<rightarrow>m" "EntryPath ns" "q \<in> phiUses m" "m \<in> set (predecessors (defNode p))"
  proof-
    from assms obtain m where m: "q \<in> phiUses m" "m \<in> set (predecessors (defNode p))"
      by (rule phiUses_exI')
    then obtain ns where "defNode q\<comment>ns\<rightarrow>m" "EntryPath ns" by - (rule defUse_path_ex[of q m], auto)
    with m show thesis by - (rule that)
  qed

  lemma phiArg_path_ex:
    assumes "phiArg p q" and[simp]: "p \<in> allVars"
    obtains ns where "defNode q\<comment>ns\<rightarrow>defNode p" "length ns > 1"
    by (rule phiArg_path_ex'[OF assms], rule, auto)

  lemma phiArg_tranclp_path_ex:
    assumes "r\<^sup>+\<^sup>+ p q" "p \<in> allVars" and[simp]: "\<And>p q. r p q \<Longrightarrow> phiArg p q"
    obtains ns where "defNode q\<comment>ns\<rightarrow>defNode p" "length ns > 1"
      "\<forall>n \<in> set (butlast ns). \<exists>p q m ns'. r p q \<and> defNode q\<comment>ns'\<rightarrow>m \<and> (defNode q) \<notin> set (tl ns') \<and> q \<in> phiUses m \<and> m \<in> set (predecessors (defNode p)) \<and> n \<in> set ns' \<and> set ns' \<subseteq> set ns \<and> defNode p \<in> set ns"
  using assms(1,2) proof (induction rule: converse_tranclp_induct)
    case (base p)
    from base.hyps base.prems(2) obtain ns' m where ns': "defNode q\<comment>ns'\<rightarrow>m" "defNode q \<notin> set (tl ns')" "m \<in> set (predecessors (defNode p))" "q \<in> phiUses m"
      by - (rule phiArg_path_ex', rule assms(3), auto intro: simple_path2)
    hence ns: "defNode q\<comment>ns'@[defNode p]\<rightarrow>defNode p" "length (ns'@[defNode p]) > 1" by auto

    show ?case
    proof (rule base.prems(1)[OF ns, rule_format], rule exI, rule exI, rule exI, rule exI)
      fix n
      assume "n \<in> set (butlast (ns' @ [defNode p]))"
      with base.hyps ns'
      show "r p q \<and>
          defNode q\<comment>ns'\<rightarrow>m \<and>
          defNode q \<notin> set (tl ns') \<and>
          q \<in> phiUses m \<and>
          m \<in> set (predecessors (defNode p)) \<and> n \<in> set ns' \<and> set ns' \<subseteq> set (ns' @ [defNode p]) \<and> defNode p \<in> set (ns' @ [defNode p])"
        by auto
    qed
  next
    case (step p p')
    from step.prems(2) step.hyps(1) obtain ns'\<^sub>2 m where ns'\<^sub>2: "defNode p'\<comment>ns'\<^sub>2\<rightarrow>m" "m \<in> set (predecessors (defNode p))" "defNode p' \<notin> set (tl ns'\<^sub>2)" "p' \<in> phiUses m"
      by - (rule phiArg_path_ex', rule assms(3), auto intro: simple_path2)
    then obtain ns\<^sub>2 where ns\<^sub>2: "defNode p'\<comment>ns\<^sub>2\<rightarrow>defNode p" "length ns\<^sub>2 > 1" "ns\<^sub>2 = ns'\<^sub>2@[defNode p]" by (atomize_elim, auto)

    show thesis
    proof (rule step.IH)
      fix ns
      assume ns: "defNode q\<comment>ns\<rightarrow>defNode p'" "1 < length ns"
      assume IH: "\<forall>n\<in>set (butlast ns).
             \<exists>p q m ns'.
                r p q \<and>
                defNode q\<comment>ns'\<rightarrow>m \<and>
                defNode q \<notin> set (tl ns') \<and>
                q \<in> phiUses m \<and> m \<in> set (predecessors (defNode p)) \<and> n \<in> set ns' \<and> set ns' \<subseteq> set ns \<and> defNode p \<in> set ns"

      let ?path = "ns@tl ns\<^sub>2"
      have ns_ns\<^sub>2: "defNode q\<comment>?path\<rightarrow>defNode p" "1 < length ?path" using ns ns\<^sub>2(1,2) by auto
      show thesis
      proof (rule step.prems(1)[OF ns_ns\<^sub>2, rule_format])
        fix n
        assume n: "n \<in> set (butlast ?path)"
        show "\<exists>p q m ns'a.
          r p q \<and>
          defNode q\<comment>ns'a\<rightarrow>m \<and>
          defNode q \<notin> set (tl ns'a) \<and>
          q \<in> phiUses m \<and> m \<in> set (predecessors (defNode p)) \<and> n \<in> set ns'a \<and> set ns'a \<subseteq> set ?path \<and> defNode p \<in> set ?path"
        proof (cases "n \<in> set (butlast ns)")
          case True
          with IH obtain p q m ns' where "
                r p q \<and>
                defNode q\<comment>ns'\<rightarrow>m \<and>
                defNode q \<notin> set (tl ns') \<and>
                q \<in> phiUses m \<and> m \<in> set (predecessors (defNode p)) \<and> n \<in> set ns' \<and> set ns' \<subseteq> set ns \<and> defNode p \<in> set ns" by auto
          thus ?thesis by - (rule exI, rule exI, rule exI, rule exI, auto)
        next
          case False
          from ns ns\<^sub>2 have 1: "?path = butlast ns@ns\<^sub>2"
            by - (rule concat_join[symmetric], auto simp: path2_def)
          from ns\<^sub>2(1) n False 1 have "n \<in> set (butlast ns\<^sub>2)" by (auto simp: butlast_append path2_not_Nil)
          with step.hyps ns'\<^sub>2 ns\<^sub>2(3) show ?thesis
            by - (subst 1, rule exI[where x=p], rule exI[where x=p'], rule exI, rule exI, auto simp: path2_not_Nil)
        qed
      qed
    next
      show "p' \<in> allVars" using step.prems(2) step.hyps(1)[THEN assms(3)] by auto
    qed
  qed

  lemma non_dominated_predecessor:
    assumes "n \<in> set \<alpha>n" "n \<noteq> Entry"
    obtains m where "m \<in> set (predecessors n)" "\<not>dominates n m"
  proof-
    obtain ns where "Entry\<comment>ns\<rightarrow>n"
      by (atomize_elim, rule Entry_reaches, auto simp add:assms(1))
    then obtain ns' where ns': "Entry\<comment>ns'\<rightarrow>n" "n \<notin> set (butlast ns')"
      by (rule simple_path2)
    let ?m = "last (butlast ns')"
    from ns'(1) assms(2) obtain m: "Entry\<comment>butlast ns'\<rightarrow>?m" "?m \<in> set (predecessors n)"
      by - (rule path2_unsnoc, auto)
    with m(1) ns'(2) show thesis
      by - (rule that, auto elim:dominatesE)
  qed

  lemma liveVal_in_allVars[simp]: "liveVal v \<Longrightarrow> v \<in> allVars"
  by (induction rule: liveVal.induct, auto intro!: allUses_in_allVars)

  lemma phi_no_closed_loop:
    assumes[simp]: "p \<in> allVars" and "phi p = Some vs"
    shows "set vs \<noteq> {p}"
  proof (cases "defNode p = Entry")
    case True
    with assms(2) show ?thesis by auto
  next
    case False
    show ?thesis
    proof
      assume[simp]: "set vs = {p}"
      let ?n = "defNode p"
      obtain ns where ns: "Entry\<comment>ns\<rightarrow>?n" "?n \<notin> set (butlast ns)" by (rule simple_Entry_path, auto)
      let ?m = "last (butlast ns)"
      from ns False obtain m: "Entry\<comment>butlast ns\<rightarrow>?m" "?m \<in> set (predecessors ?n)"
        by - (rule path2_unsnoc, auto)
      hence "p \<in> phiUses ?m" using assms(2) by - (rule phiUses_exI, auto simp:phi_def)
      hence "defAss ?m p" using m by - (rule allUses_def_ass, auto)
      then obtain l where l: "l \<in> set (butlast ns)" "p \<in> allDefs l" using m by - (drule defAssD, auto)
      with assms(2) m have "l = ?n" by - (rule allDefs_disjoint', auto)
      with ns l m show False by auto
    qed
  qed

  lemma phis_phi: "phis (n, v) = Some vs \<Longrightarrow> phi v = Some vs"
  unfolding phi_def
  apply (subst defNode_eq)
  by (auto simp: allDefs_def phi_def phiDefs_def intro: phis_in_\<alpha>n)

  lemma trivial_phi: "trivial v \<Longrightarrow> phi v \<noteq> None"
  by (auto simp: trivial_def isTrivialPhi_def split: option.splits)

  lemma trivial_finite: "finite {v. trivial v}"
  by (rule finite_subset[OF _ phi_finite]) (auto dest: trivial_phi)

  lemma trivial_in_allVars: "trivial v \<Longrightarrow> v \<in> allVars"
  by (drule trivial_phi, auto simp: allDefs_def phiDefs_def image_def phi_def intro: phis_in_\<alpha>n intro!: allDefs_in_allVars)

  declare phiArg_def [simp del]
end

subsection {* Bundling of CFG and Equivalent SSA CFG *}

locale CFG_SSA_Transformed_base = CFG_SSA_wf_base \<alpha>n predecessors Entry "defs" "uses" phis
  + old: CFG_base \<alpha>n predecessors Entry oldDefs oldUses
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  oldDefs :: "'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'node \<Rightarrow> 'var set" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'node \<Rightarrow> 'val set" and
  phis :: " ('node, 'val) phis" +
  fixes var :: "'val \<Rightarrow> 'var"

locale CFG_SSA_Transformed = CFG_SSA_Transformed_base \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var
  + CFG_SSA_wf \<alpha>n predecessors Entry "defs" "uses" phis
  + old: CFG_wf \<alpha>n predecessors Entry oldDefs oldUses
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
  assumes oldDefs_def: "oldDefs n = var ` defs n"
  assumes oldUses_def: "n \<in> set \<alpha>n \<Longrightarrow> oldUses n = var ` uses n"
  assumes conventional: "
\<lbrakk>n\<comment>ns\<rightarrow>m; n \<notin> set (tl ns); v \<in> allDefs n; v \<in> allUses m; x \<in> set (tl ns); v' \<in> allDefs x\<rbrakk> \<Longrightarrow> var v' \<noteq> var v"
  assumes phis_same_var[elim]: "phis (n,v) = Some vs \<Longrightarrow> v' \<in> set vs \<Longrightarrow> var v' = var v"
  assumes allDefs_var_disjoint: "\<lbrakk>n \<in> set \<alpha>n; v \<in> allDefs n; v' \<in> allDefs n; v \<noteq> v'\<rbrakk> \<Longrightarrow> var v' \<noteq> var v"
begin
  lemma conventional': "\<lbrakk>n\<comment>ns\<rightarrow>m; n \<notin> set (tl ns); v \<in> allDefs n; v \<in> allUses m; v' \<in> allDefs x; var v' = var v\<rbrakk> \<Longrightarrow> x \<notin> set (tl ns)"
    using conventional by auto

  lemma conventional'': "\<lbrakk>defNode v\<comment>ns\<rightarrow>m; defNode v \<notin> set (tl ns); v \<in> allUses m; var v' = var v; v \<in> allVars; v' \<in> allVars\<rbrakk> \<Longrightarrow> defNode v' \<notin> set (tl ns)"
    by (rule conventional'[where v=v and v'=v'], auto)

  lemma phiArg_same_var: "phiArg p q \<Longrightarrow> var q = var p"
    by (metis phiArg_def phi_def phis_same_var)

  lemma oldDef_defAss:
    assumes "v \<in> allUses n" "Entry\<comment>ns\<rightarrow>n"
    obtains m where "m \<in> set ns" "var v \<in> oldDefs m"
  using assms proof (induction ns arbitrary: v n rule: length_induct)
    case (1 ns)
    from "1.prems"(2-) have 2: "defNode v \<in> set ns"
      by - (rule defAss_defNode, rule allUses_def_ass, auto)
    let ?V = "defNode v"
    from "1.prems"(2,3) have[simp]: "v \<in> allVars" by auto
    thus ?case
    proof (cases v rule: defNode_cases)
      case simpleDef
      with 2 show thesis by - (rule "1.prems"(1), auto simp: oldDefs_def)
    next
      case phi
      then obtain vs where vs: "phi v = Some vs" by auto
      from "1.prems"(3) 2 obtain ns' where ns': "Entry\<comment>ns'\<rightarrow>?V" "prefixeq ns' ns"
        by (rule path2_split_ex, auto)
      let ?V' = "last (butlast ns')"
      from ns' phi have nontriv: "length ns' \<ge> 2"
        by - (rule path2_nontrivial, auto)
      hence 3: "Entry\<comment>butlast ns'\<rightarrow>?V'" "?V' \<in> set (predecessors ?V)"
        using ns'(1) by (auto intro: path2_unsnoc)
      with phi vs obtain v' where v': "v' \<in> phiUses ?V'" "var v' = var v"
        by - (rule phiArg_exI, auto simp: phi_def phis_same_var phiArg_def)
      show thesis
      proof (rule "1.IH"[rule_format])
        show "length (butlast ns') < length ns" using ns' by (cases ns', auto simp: path2_not_Nil2 dest: prefixeq_length_le)
        show "v' \<in> allUses ?V'" using v'(1) by simp
      next
        fix n
        assume "n \<in> set (butlast ns')" "var v' \<in> oldDefs n"
        thus thesis
          using ns'(2)[THEN set_mono_prefixeq] v'(2) by - (rule "1.prems"(1)[of n], auto dest: in_set_butlastD)
      qed (rule 3(1))
    qed
  qed

  lemma allDef_path_from_simpleDef:
    assumes[simp]: "v \<in> allVars"
    obtains n ns where "n\<comment>ns\<rightarrow>defNode v" "EntryPath ns" "var v \<in> oldDefs n"
  proof-
    let ?V = "defNode v"
    from assms obtain ns where ns: "Entry\<comment>ns\<rightarrow>?V" "EntryPath ns"
      by - (rule Entry_reachesE, auto)
    from assms show thesis
    proof (cases v rule: defNode_cases)
      case simpleDef
      thus thesis by - (rule that, auto simp: oldDefs_def)
    next
      case phi
      then obtain vs where vs: "phi v = Some vs" by auto
      let ?V' = "last (butlast ns)"
      from ns phi have nontriv: "length ns \<ge> 2"
        by - (rule path2_nontrivial, auto)
      hence 3: "Entry\<comment>butlast ns\<rightarrow>?V'" "?V' \<in> set (predecessors ?V)"
        using ns(1) by (auto intro: path2_unsnoc)
      with phi vs obtain v' where v': "v' \<in> phiUses ?V'" "var v' = var v"
        by - (rule phiArg_exI, auto simp: phi_def phis_same_var phiArg_def)
      with 3(1) obtain n where n: "n \<in> set (butlast ns)" "var v' \<in> oldDefs n"
        by - (rule oldDef_defAss[of v'], auto)
      with ns obtain ns' where "n\<comment>ns'\<rightarrow>?V" "suffixeq ns' ns"
        by - (rule path2_split_ex'[OF ns(1)], auto intro: in_set_butlastD simp: suffixeq_def)
      with n(2) v'(2) ns(2) show thesis
        by - (rule that, assumption, erule EntryPath_suffixeq, auto)
    qed
  qed

  lemma defNode_var_disjoint:
    assumes "p \<in> allVars" "q \<in> allVars" "p \<noteq> q" "defNode p = defNode q"
    shows "var p \<noteq> var q"
  proof-
    have "q \<in> allDefs (defNode p)" using assms(2) assms(4) by (auto)
    thus ?thesis using assms(1-3)
      by - (rule allDefs_var_disjoint[of "defNode p"], auto)
  qed

  lemma phiArg_distinct_nodes:
    assumes "phiArg p q" "p \<noteq> q" and[simp]: "p \<in> allVars"
    shows "defNode p \<noteq> defNode q"
  proof
    have "p \<in> allDefs (defNode p)" by simp
    moreover assume "defNode p = defNode q"
    ultimately have "var p \<noteq> var q" using assms
      by - (rule defNode_var_disjoint, auto)
    moreover
    from assms(1) have "var q = var p" by (rule phiArg_same_var)
    ultimately show False by simp
  qed

  lemma phiArgs_def_distinct:
    assumes "phiArg p q" "phiArg p r" "q \<noteq> r" "p \<in> allVars"
    shows "defNode q \<noteq> defNode r"
  proof (rule)
    assume "defNode q = defNode r"
    hence "var q \<noteq> var r" using assms by - (rule defNode_var_disjoint, auto)
    thus False using phiArg_same_var[OF assms(1)] phiArg_same_var[OF assms(2)] by simp
  qed

  lemma defNode_not_on_defUse_path:
    assumes p: "defNode p\<comment>ns\<rightarrow>n" "defNode p \<notin> set (tl ns)" "p \<in> allUses n"
    assumes[simp]: "q \<in> allVars" "p \<noteq> q" "var p = var q"
    shows "defNode q \<notin> set ns"
  proof-
    let ?P = "defNode p"
    let ?Q = "defNode q"

    have[simp]: "p \<in> allVars" using p(1,3) by auto
    have "?P \<noteq> ?Q" using defNode_var_disjoint[of p q] by auto
    moreover have "?Q \<notin> set (tl ns)" using p(2,3)
      by - (rule conventional'[OF p(1), of p q], auto)
    ultimately show ?thesis using p(1) by (cases ns, auto simp: path2_def)
  qed

  lemma defUse_paths_disjoint:
    assumes p: "defNode p\<comment>ns\<rightarrow>n" "defNode p \<notin> set (tl ns)" "p \<in> allUses n"
    assumes q: "defNode q\<comment>ms\<rightarrow>m" "defNode q \<notin> set (tl ms)" "q \<in> allUses m"
    assumes[simp]: "p \<noteq> q" "var p = var q"
    shows "set ns \<inter> set ms = {}"
  proof (rule equals0I)
    fix y
    assume y: "y \<in> set ns \<inter> set ms"

    {
      fix p ns n
      assume p: "defNode p\<comment>ns\<rightarrow>n" "defNode p \<notin> set (tl ns)" "p \<in> allUses n"
      assume y: "y \<in> set ns"
      from p(1,3) have dom: "dominates (defNode p) n" by - (rule allUses_dominated, auto)
      moreover
      obtain ns' where "y\<comment>ns'\<rightarrow>n" "suffixeq ns' ns"
        by (rule path2_split_first_last[OF p(1) y], auto)
      ultimately have "dominates (defNode p) y" using suffixeq_tl_subset[of ns' ns] p(2)
        by - (rule dominates_extend[where ms=ns'], auto)
    }
    with assms y have dom: "dominates (defNode p) y" "dominates (defNode q) y" by auto

    {
      fix p ns n q ms m
      let ?P = "defNode p"
      let ?Q = "defNode q"

      assume p: "defNode p\<comment>ns\<rightarrow>n" "defNode p \<notin> set (tl ns)" "p \<in> allUses n" "dominates ?P y" "y \<in> set ns"
      assume q: "defNode q\<comment>ms\<rightarrow>m" "defNode q \<notin> set (tl ms)" "q \<in> allUses m" "dominates ?Q y" "y \<in> set ms"
      assume[simp]: "p \<noteq> q" "var p = var q"
      assume dom: "dominates ?P ?Q"
      then obtain pqs where pqs: "?P\<comment>pqs\<rightarrow>?Q" "?P \<notin> set (tl pqs)" by (rule dominates_path, auto intro: simple_path2)
      from p obtain ns\<^sub>2 where ns\<^sub>2: "y\<comment>ns\<^sub>2\<rightarrow>n" "suffixeq ns\<^sub>2 ns" by - (rule path2_split_first_last, auto)
      from q obtain ms\<^sub>1 where ms\<^sub>1: "?Q\<comment>ms\<^sub>1\<rightarrow>y" "prefixeq ms\<^sub>1 ms" by - (rule path2_split_first_last, auto)
      have "var q \<noteq> var p"
      proof (rule conventional[OF _ _ _ p(3)])
        let ?path = "(pqs@tl ms\<^sub>1)@tl ns\<^sub>2"
        show "?P\<comment>?path\<rightarrow>n" using pqs ms\<^sub>1 ns\<^sub>2
          by (auto simp del:append_assoc intro:path2_app)
        have "?P \<notin> set (tl ns\<^sub>2)" using p(2) ns\<^sub>2(2)[THEN suffixeq_tl_subset, THEN subsetD] by auto
        moreover
        have[simp]: "q \<in> allVars" "p \<in> allVars" using p q by auto
        have "?P \<notin> set (tl ms)" using q
          by - (rule conventional'[where v'=p and v=q], auto)
        hence "?P \<notin> set (tl ms\<^sub>1)" using ms\<^sub>1(2)[simplified, THEN prefixeq_tl_subset] by auto
        ultimately
        show "?P \<notin> set (tl ?path)" using pqs(2)
          by - (rule notI, auto dest: subsetD[OF set_tl_append'])
        show "p \<in> allDefs (defNode p)" by auto
        have "?P \<noteq> ?Q" using defNode_var_disjoint[of p q] by auto
        hence 1: "length pqs > 1" using pqs by - (rule path2_nontriv)
        hence "?Q \<in> set (tl pqs)" using pqs unfolding path2_def by (auto intro:last_in_tl)
        moreover from 1 have "pqs \<noteq> []" by auto
        ultimately show "?Q \<in> set (tl ?path)" by simp
        show "q \<in> allDefs ?Q" by simp
      qed
      hence False by simp
    }
    from this[OF p _ _ q] this[OF q _ _ p] y dom show False
      by - (rule dominates_antitrans[OF dom], auto)
  qed

  lemma oldDefsI: "v \<in> defs n \<Longrightarrow> var v \<in> oldDefs n" by (simp add: oldDefs_def)

  lemma simpleDefs_phiDefs_var_disjoint:
    assumes "v \<in> phiDefs n" "n \<in> set \<alpha>n"
    shows "var v \<notin> oldDefs n"
  proof
    from assms have[simp]: "v \<in> allVars" by auto
    assume "var v \<in> oldDefs n"
    then obtain v'' where v'': "v'' \<in> defs n" "var v'' = var v"
      by (auto simp: oldDefs_def)
    from this(1) assms have "v'' \<noteq> v"
      using simpleDefs_phiDefs_disjoint[of n] by (auto simp: phiArg_def)
    with v'' assms show False
      using allDefs_var_disjoint[of n v'' v] by auto
  qed

  lemma liveVal_use_path:
    assumes "liveVal v"
    obtains ns m where "defNode v\<comment>ns\<rightarrow>m" "var v \<in> oldUses m"
      "\<And>x. x \<in> set (tl ns) \<Longrightarrow> var v \<notin> oldDefs x"
  using assms proof (induction)
    case (liveSimple m v)
    from liveSimple.hyps have[simp]: "v \<in> allVars"
      by - (rule allUses_in_allVars, auto)
    from liveSimple.hyps obtain ns where ns: "defNode v\<comment>ns\<rightarrow>m" "defNode v \<notin> set (tl ns)"
      by - (rule defUse_path_ex, auto intro!: uses_in_allUses elim: simple_path2)
    from this(1) show thesis
    proof (rule liveSimple.prems)
      show "var v \<in> oldUses m" using liveSimple.hyps by (auto simp: oldUses_def)
      {
        fix x
        assume asm: "x \<in> set (tl ns)" "var v \<in> oldDefs x"
        then obtain v' where "v' \<in> defs x" "var v' = var v"
          by (auto simp: oldDefs_def)
        with asm liveSimple.hyps have False
          by - (rule conventional[OF ns, of v x v', THEN notE], auto)
      }
      thus "\<And>x. x \<in> set (tl ns) \<Longrightarrow> var v \<notin> oldDefs x" by auto
    qed
  next
    case (livePhi v v')
    from livePhi.hyps have[simp]: "v \<in> allVars" "v' \<in> allVars" "var v' = var v"
      by (auto intro: phiArg_same_var)
    show thesis
    proof (rule livePhi.IH)
      fix ns m
      assume asm: "defNode v\<comment>ns\<rightarrow>m" "var v \<in> oldUses m"
        "\<And>x. x \<in> set (tl ns) \<Longrightarrow> var v \<notin> oldDefs x"
      from livePhi.hyps(2) obtain ns' m' where ns': "defNode v'\<comment>ns'\<rightarrow>m'" "v' \<in> phiUses m'"
        "m' \<in> set (predecessors (defNode v))" "defNode v' \<notin> set (tl ns')"
        by (rule phiArg_path_ex', auto elim: simple_path2)
      show thesis
      proof (rule livePhi.prems)
        show "defNode v'\<comment>(ns'@[defNode v])@tl ns\<rightarrow>m"
        apply (rule path2_app)
         apply (rule path2_snoc[OF ns'(1,3)])
        by (rule asm(1))
        show "var v' \<in> oldUses m" using asm(2) by simp
        {
          fix x
          assume asm: "x \<in> set (tl ns')" "var v \<in> oldDefs x"
          then obtain v'' where "v'' \<in> defs x" "var v'' = var v"
            by (auto simp: oldDefs_def)
          with asm ns'(2) have False
            by - (rule conventional[OF ns'(1,4), of v' x v'', THEN notE], auto)
        }
        then show "\<And>x. x \<in> set (tl ((ns'@[defNode v])@tl ns)) \<Longrightarrow> var v' \<notin> oldDefs x"
          using simpleDefs_phiDefs_var_disjoint[of v "defNode v"] livePhi.hyps(2)
          by (auto dest!: set_tl_append'[THEN subsetD] asm(3) simp: phiArg_def)
      qed
    qed
  qed
end

end
