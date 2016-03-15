(*  Title:      Construct_SSA_notriv_code.thy
    Author:     Denis Lohner, Sebastian Ullrich
*)

subsection {* Code Equations for SSA Minimization *}

theory Construct_SSA_notriv_code imports
  SSA_CFG_code
  Construct_SSA_notriv
  While_Combinator_Exts
begin

abbreviation (input) "const x \<equiv> (\<lambda>_. x)"

context CFG_SSA_Transformed_notriv_base begin
  definition [code]: "substitution_code next = the (the_trivial (snd next) (the (phis next)))"
  definition [code]: "substNext_code next \<equiv> \<lambda>v. if v = snd next then substitution_code next else v"
  definition [code]: "uses'_code next n \<equiv> substNext_code next ` uses n"

  lemma substNext_code_alt_def:
    "substNext_code next = id(snd next := substitution_code next)"
    unfolding substNext_code_def by auto
end

type_synonym ('node, 'val) chooseNext_code = "('node \<Rightarrow> 'val set) \<Rightarrow> ('node, 'val) phis_code \<Rightarrow> ('node \<times> 'val)"

locale CFG_SSA_Transformed_notriv_base_code =
  ssa:CFG_SSA_wf_base_code \<alpha>n predecessors Entry "defs" "uses" phis +
  CFG_SSA_Transformed_notriv_base \<alpha>n predecessors Entry oldDefs oldUses "defs" "usesOf uses" "Mapping.lookup phis" var "\<lambda>uses phis. chooseNext_all uses (Mapping.Mapping phis)"
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  oldDefs :: "'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'node \<Rightarrow> 'var set" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: " ('node, 'val set) mapping" and
  phis :: " ('node, 'val) phis_code" and
  var :: "'val \<Rightarrow> 'var" and
  chooseNext_all :: "('node, 'val) chooseNext_code"
begin
  definition [code]: "cond_code = ssa.redundant_code"

  definition uses'_codem :: "'node \<times> 'val \<Rightarrow> 'val \<Rightarrow> ('val, 'node set) mapping \<Rightarrow> ('node, 'val set) mapping"
  where [code]: "uses'_codem next next' nodes_of_uses =
    fold (\<lambda>n. Mapping.update n (Set.insert next' (Set.remove (snd next) (the (Mapping.lookup uses n)))))
      (sorted_list_of_set (case_option {} id (Mapping.lookup nodes_of_uses (snd next))))
      uses"

  definition nodes_of_uses' :: "'node \<times> 'val \<Rightarrow> 'val \<Rightarrow> 'val set \<Rightarrow> ('val, 'node set) mapping \<Rightarrow> ('val, 'node set) mapping"
  where [code]: "nodes_of_uses' next next' phiVals nodes_of_uses =
    (let users = case_option {} id (Mapping.lookup nodes_of_uses (snd next))
    in
    if (next' \<in> phiVals) then Mapping.map_default next' {} (\<lambda>ns. ns \<union> users) (Mapping.delete (snd next) nodes_of_uses)
    else Mapping.delete (snd next) nodes_of_uses)"

  (* FIXME: phis'_code ist in O(n) \<rightarrow> verwende nodes_of_uses ? *)
  definition [code]: "phis'_code next \<equiv> map_values (\<lambda>(n,v) vs. if v = snd next then None else Some (map (substNext_code next) vs)) phis"

  (* Schon besser: O(log(n)) *)
  definition [code]: "phis'_codem next next' nodes_of_phis =
    fold (\<lambda>n. Mapping.update n (List.map (id(snd next := next')) (the (Mapping.lookup phis n))))
      (sorted_list_of_set (case_option {} (Set.remove next) (Mapping.lookup nodes_of_phis (snd next))))
      (Mapping.delete next phis)"

  definition nodes_of_phis' :: "'node \<times> 'val \<Rightarrow> 'val \<Rightarrow> ('val, ('node \<times> 'val) set) mapping \<Rightarrow> ('val, ('node \<times> 'val) set) mapping"
  where [code]: "nodes_of_phis' next next' nodes_of_phis =
      (let old_phis = Set.remove next (case_option {} id (Mapping.lookup nodes_of_phis (snd next)));
        nop = Mapping.delete (snd next) nodes_of_phis
      in
      Mapping.map_default next' {} (\<lambda>ns. (Set.remove next ns) \<union> old_phis) nop)"

  definition [code]: "triv_phis' next triv_phis nodes_of_phis
    = (Set.remove next triv_phis) \<union> (Set.filter (\<lambda>n. ssa.trivial_code (snd n) (the (Mapping.lookup phis n))) (case_option {} (Set.remove next) (Mapping.lookup nodes_of_phis (snd next))))"

  definition [code]: "step_code = (let next = chooseNext' in (uses'_code next, phis'_code next))"
  definition [code]: "step_codem next next' nodes_of_uses nodes_of_phis = (uses'_codem next next' nodes_of_uses, phis'_codem next next' nodes_of_phis)"

  definition phi_equiv_mapping :: " ('val, 'a set) mapping \<Rightarrow> ('val, 'a set) mapping \<Rightarrow> bool" ("_ \<approx>\<^sub>\<phi> _" 50)
    where "nou\<^sub>1 \<approx>\<^sub>\<phi> nou\<^sub>2 \<equiv> \<forall>v \<in> Mapping.keys (ssa.phidefNodes). case_option {} id (Mapping.lookup nou\<^sub>1 v) = case_option {} id (Mapping.lookup nou\<^sub>2 v)"
end

locale CFG_SSA_Transformed_notriv_linorder = CFG_SSA_Transformed_notriv_base \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
   + CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  oldDefs :: "'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'node \<Rightarrow> 'var set" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'node \<Rightarrow> 'val set" and
  phis :: " ('node, 'val) phis" and
  var :: "'val \<Rightarrow> 'var" and
  chooseNext_all :: "('node \<Rightarrow> 'val set) \<Rightarrow> ('node, 'val) phis \<Rightarrow> ('node \<times> 'val)"
begin
  lemma isTrivial_the_trivial: "\<lbrakk> phi v = Some vs; isTrivialPhi v v' \<rbrakk> \<Longrightarrow> the_trivial v vs = Some v'"
    by (subst the_trivialI [of vs v v']) (auto simp: isTrivialPhi_def)

  lemma the_trivial_THE_isTrivial: "\<lbrakk> phi v = Some vs; trivial v \<rbrakk> \<Longrightarrow> the_trivial v vs = Some (The (isTrivialPhi v))"
    apply (frule isTrivialPhi_det)
    apply clarsimp
    apply (frule(1) isTrivial_the_trivial)
    by (auto dest: isTrivial_the_trivial intro!: the_equality intro: sym)

  lemma substitution_code_correct:
    assumes "redundant"
    shows "substitution = substitution_code (chooseNext')"
  proof -
    from substitution [OF assms] have "phi (chooseNext) \<noteq> None"
      unfolding isTrivialPhi_def by (clarsimp split: option.splits)
    then obtain vs where "phi (chooseNext) = Some vs" by blast
    with isTrivial_the_trivial [OF this substitution [OF assms]] chooseNext'[OF assms]
    show ?thesis unfolding substitution_code_def by (auto simp: phis_phi[of "fst (chooseNext')"])
  qed

  lemma substNext_code_correct:
    assumes "redundant"
    shows "substNext = substNext_code (chooseNext')"
    unfolding substNext_def [abs_def] substNext_code_def
    by (auto simp: substitution_code_correct [OF assms])

  lemma uses'_code_correct:
    assumes "redundant"
    shows "uses' = uses'_code (chooseNext')"
    unfolding uses'_def [abs_def] uses'_code_def [abs_def]
    by (auto simp: substNext_code_correct [OF assms])

end

context CFG_SSA_Transformed_notriv_linorder
begin
  lemma substAll_terminates: "while_option (cond) (step) (uses, phis) \<noteq> None"
  apply (rule notI)
  apply (rule while_option_None_invD [where I="inst'" and r="{(y,x). (inst' x \<and> cond x) \<and> y = step x}"], assumption)
     apply (rule wf_if_measure[where f="\<lambda>(u,p). card (dom p)"])
     defer
     apply simp
     apply unfold_locales
    apply (case_tac s)
    apply (simp add: step_def cond_def)
    apply (rule step_preserves_inst [unfolded step_def, simplified], assumption+)
   apply (simp add: step_def cond_def)
  apply (clarsimp simp: cond_def step_def split:prod.split)
  proof-
    fix u p
    assume "CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses defs u p var chooseNext_all"
    then interpret i: CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses "defs" u p var chooseNext_all .
    assume "i.redundant"
    thus "card (dom (i.phis')) < card (dom p)" by (rule i.substAll_wf)
  qed
end

locale CFG_SSA_Transformed_notriv_linorder_code =
  CFG_SSA_Transformed_code \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var
+ CFG_SSA_Transformed_notriv_base_code \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
+ CFG_SSA_Transformed_notriv_linorder \<alpha>n predecessors Entry oldDefs oldUses "defs" "usesOf uses" "Mapping.lookup phis" var
  "\<lambda>uses phis. chooseNext_all uses (Mapping.Mapping phis)"
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  oldDefs :: "'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'node \<Rightarrow> 'var set" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: " ('node, 'val set) mapping" and
  phis :: " ('node, 'val) phis_code" and
  var :: "'val \<Rightarrow> 'var" and
  chooseNext_all :: "('node, 'val) chooseNext_code"
+
assumes chooseNext_all_code:
  "CFG_SSA_Transformed_code \<alpha>n predecessors Entry oldDefs oldUses defs u p var \<Longrightarrow>
  CFG_SSA_wf_base_code.redundant_code p \<Longrightarrow>
  chooseNext_all (usesOf (u)) (p) = Max (CFG_SSA_wf_base_code.trivial_phis p)"

locale CFG_SSA_step_code =
  CFG_SSA_Transformed_notriv_linorder_code \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
+
  CFG_SSA_step \<alpha>n predecessors Entry oldDefs oldUses "defs" "usesOf uses" "Mapping.lookup phis" var "\<lambda>uses phis. chooseNext_all uses (Mapping.Mapping phis)"
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry::"'node" and
  oldDefs :: "'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'node \<Rightarrow> 'var set" and
  "defs" :: "'node \<Rightarrow> 'val::linorder set" and
  "uses" :: " ('node, 'val set) mapping" and
  phis :: " ('node, 'val) phis_code" and
  var :: "'val \<Rightarrow> 'var" and
  chooseNext_all :: "('node, 'val) chooseNext_code"

context CFG_SSA_Transformed_notriv_linorder_code
begin
  abbreviation "cN \<equiv> (\<lambda>uses phis. chooseNext_all uses (Mapping.Mapping phis))"

  interpretation uninst_code: CFG_SSA_Transformed_notriv_base_code \<alpha>n predecessors Entry oldDefs oldUses "defs" u p var chooseNext_all
    for u p
  by unfold_locales

  interpretation uninst: CFG_SSA_Transformed_notriv_base \<alpha>n predecessors Entry oldDefs oldUses "defs" u p var cN
    for u p
  by unfold_locales

  lemma phis'_code_correct:
    assumes "ssa.redundant"
    shows "phis' = Mapping.lookup (phis'_code (chooseNext'))"
  unfolding phis'_def [abs_def] phis'_code_def [abs_def]
  by (auto simp: Mapping_lookup_map_values substNext_code_correct [OF assms] split: split_if Option.bind_split)

  lemma set_sorted_list_of_set_phis_dom [simp]:
  "set (sorted_list_of_set {x \<in> dom (Mapping.lookup phis). P x}) = {x \<in> dom (Mapping.lookup phis). P x}"
  apply (subst sorted_list_of_set)
  by (rule finite_subset [OF _ ssa.phis_finite [of]]) auto

  lemma phis'_codem_correct:
    assumes "nodes_of_phis \<approx>\<^sub>\<phi> (ssa.phiNodes_of)" and "next \<in> Mapping.keys phis"
    shows "phis'_codem next (substitution_code next) nodes_of_phis = phis'_code next"
  proof -
    from assms
    have "phis'_code next = mmap (map (substNext_code next)) (Mapping.delete next phis)"
      unfolding phis'_code_def mmap_def phi_equiv_mapping_def
    apply (subst mapping_eq_iff)
    by (auto simp: Mapping_lookup_map_values Mapping_lookup_map Option.bind_def map_option_case lookup_delete keys_dom_lookup
      dest: ssa.phis_disj [where n="fst next" and v="snd next", simplified] split: option.splits)

    also from assms have "... = phis'_codem next (substitution_code next) nodes_of_phis"
      unfolding phis'_codem_def mmap_def ssa.lookup_phiNodes_of [OF ssa.phis_finite] phi_equiv_mapping_def
    apply (subst mapping_eq_iff)
    apply (simp add: Mapping_lookup_map lookup_delete map_option_case)
    by (erule_tac x="next" in ballE)
    (force intro!: map_idI
      simp: substNext_code_def keys_dom_lookup fun_upd_apply
      split: option.splits if_splits)+
    finally show ?thesis ..
  qed

  lemma uses_transfer [transfer_rule]: "(pcr_mapping op = op =) (\<lambda>n. Mapping.lookup uses n) uses"
    by (auto simp: mapping.pcr_cr_eq cr_mapping_def Mapping.lookup.rep_eq)

  lemma uses'_codem_correct:
  assumes "nodes_of_uses \<approx>\<^sub>\<phi> ssa.useNodes_of" and "next \<in> Mapping.keys phis"
  shows "usesOf (uses'_codem next (substitution_code next) nodes_of_uses) = uses'_code next"
  using dom_uses_in_graph [of] assms
  unfolding uses'_codem_def uses'_code_def [abs_def]
  apply (clarsimp simp: mmap_def Mapping.replace_def [abs_def] phi_equiv_mapping_def intro!: ext)
  apply (transfer' fixing:)
  apply (subgoal_tac "\<And>b. finite
             {n. (\<exists>y. Mapping.lookup uses n = Some y) \<and>
                 (\<forall>x2. Mapping.lookup uses n = Some x2 \<longrightarrow> n \<in> set \<alpha>n \<and> b \<in> x2)}")
   prefer 2
   apply (rule finite_subset [where B="set \<alpha>n"])
    apply (clarsimp simp: Mapping.keys_dom_lookup)
   apply simp
  by (auto simp: map_of_map_restrict restrict_map_def substNext_code_def fold_update_conv Mapping.keys_dom_lookup
    split: option.splits)

  lemma cN_transfer [transfer_rule]: "(rel_fun op = (rel_fun (pcr_mapping op = op =) op =)) cN chooseNext_all"
    by (auto simp: rel_fun_def mapping.pcr_cr_eq cr_mapping_def mapping.rep_inverse)

  lemma usesOf_transfer [transfer_rule]: "(rel_fun (pcr_mapping op = op =) op =) (\<lambda>m x. case_option {} id (m x))  usesOf"
    by (auto simp: rel_fun_def mapping.pcr_cr_eq cr_mapping_def Mapping.lookup.rep_eq)

  lemma dom_phis'_codem:
  assumes "\<And>ns. Mapping.lookup nodes_of_phis (snd next) = Some ns \<Longrightarrow> finite ns"
  shows "dom (Mapping.lookup (phis'_codem next next' nodes_of_phis)) = dom (Mapping.lookup phis) \<union> (case_option {} id (Mapping.lookup nodes_of_phis (snd next))) - {next}"
    using assms unfolding phis'_codem_def
    by (auto split: if_splits option.splits  simp: lookup_delete)

  lemma dom_phis'_code [simp]:
  shows "dom (Mapping.lookup (phis'_code next)) = dom (Mapping.lookup phis) - {v. snd v = snd next}"
    unfolding phis'_code_def by (auto simp: Mapping_lookup_map_values Option.bind_def split: option.splits)

  lemma nodes_of_phis_finite [simplified]:
  assumes "nodes_of_phis \<approx>\<^sub>\<phi> ssa.phiNodes_of" and "Mapping.lookup nodes_of_phis v = Some ns" and "v \<in> Mapping.keys (ssa.phidefNodes)"
  shows "finite ns"
  using assms unfolding phi_equiv_mapping_def
    by (erule_tac x=v in ballE) (auto intro: finite_subset [OF _ ssa.phis_finite [of]])

  lemma lookup_phis'_codem_next:
  assumes "\<And>ns. Mapping.lookup nodes_of_phis (snd next) = Some ns \<Longrightarrow> finite ns"
  shows "Mapping.lookup (phis'_codem next next' nodes_of_phis) next = None"
    using assms unfolding phis'_codem_def
    by (auto simp: Set.remove_def lookup_delete split: option.splits)

  lemma lookup_phis'_codem_other:
  assumes "nodes_of_phis \<approx>\<^sub>\<phi> (ssa.phiNodes_of)"
  and "next \<in> Mapping.keys phis" and "next \<noteq> \<phi>"
  shows "Mapping.lookup (phis'_codem next (substitution_code next) nodes_of_phis) \<phi> =
    map_option (map (substNext_code next)) (Mapping.lookup phis \<phi>)"
  proof (cases "snd next \<noteq> snd \<phi>")
    case True
    with assms(1,2) show ?thesis
      unfolding phis'_codem_correct [OF assms(1,2)] phis'_code_def
      using assms(3)
      by (auto intro!: map_idI [symmetric] simp: Mapping_lookup_map_values substNext_code_def lookup_delete map_option_case split: option.splits prod.splits)
  next
    case False
    hence "snd next = snd \<phi>" by simp
    with assms(3) have "fst next \<noteq> fst \<phi>" by (cases "next", cases \<phi>) auto
    with assms(2) False have [simp]: "Mapping.lookup phis \<phi> = None"
      by (cases \<phi>, cases "next") (fastforce simp: keys_dom_lookup dest: ssa.phis_disj)
    from `fst next \<noteq> fst \<phi>` `snd next = snd \<phi>` show ?thesis
    unfolding phis'_codem_correct [OF assms(1,2)] phis'_code_def
      by (auto simp: Mapping_lookup_map_values lookup_delete map_option_case substNext_code_def split: option.splits)
  qed

  lemma lookup_nodes_of_phis'_subst [simp]:
  "Mapping.lookup (nodes_of_phis' next (substitution_code next) nodes_of_phis) (substitution_code next) =
    Some ((case_option {} (Set.remove next) (Mapping.lookup nodes_of_phis (substitution_code next))) \<union> (case_option {} (Set.remove next) (Mapping.lookup nodes_of_phis (snd next))))"
  unfolding nodes_of_phis'_def
    by (clarsimp simp: Mapping_lookup_map_default Set.remove_def lookup_delete split: option.splits)

  lemma lookup_nodes_of_phis'_not_subst:
  "v \<noteq> substitution_code next \<Longrightarrow>
  Mapping.lookup (nodes_of_phis' next (substitution_code next) nodes_of_phis) v = (if v = snd next then None else Mapping.lookup nodes_of_phis v)"
  unfolding nodes_of_phis'_def
    by (clarsimp simp: Mapping_lookup_map_default lookup_delete)

  lemma lookup_phis'_code:
  "Mapping.lookup (phis'_code next) v = (if snd v = snd next then None else map_option (map (substNext_code next)) (Mapping.lookup phis v))"
    unfolding phis'_code_def
    by (auto simp: Mapping_lookup_map_values Option.bind_def split: option.splits prod.splits)

  lemma phi_equiv_mappingE':
    assumes "m\<^sub>1 \<approx>\<^sub>\<phi> ssa.phiNodes_of"
    and "Mapping.lookup phis x = Some vs" and "b \<in> set vs" and "b \<in> snd ` Mapping.keys phis"
    obtains "Mapping.lookup m\<^sub>1 b = Some {n \<in> Mapping.keys phis. b \<in> set (the (Mapping.lookup phis n))}"
    using assms unfolding phi_equiv_mapping_def
    apply (auto split: option.splits if_splits)
    apply (clarsimp simp: keys_dom_lookup)
    apply (rename_tac n \<phi>_args)
    apply (erule_tac x="(n,b)" in ballE)
     prefer 2 apply auto[1]
    by (cases x) force

  lemma phi_equiv_mappingE:
    assumes "m\<^sub>1 \<approx>\<^sub>\<phi> ssa.phiNodes_of" and "b \<in> Mapping.keys phis"
    and "Mapping.lookup phis x = Some vs" and "snd b \<in> set vs"
    obtains ns where "Mapping.lookup m\<^sub>1 (snd b) = Some {n \<in> Mapping.keys phis. snd b \<in> set (the (Mapping.lookup phis n))}"
  proof -
    from assms(2) have "snd b \<in> snd ` Mapping.keys phis" by simp
    with assms(1,3,4) show ?thesis
    by (rule phi_equiv_mappingE') (rule that)
  qed

  lemma phi_equiv_mappingE2':
    assumes "m\<^sub>1 \<approx>\<^sub>\<phi> ssa.phiNodes_of"
    and "b \<in> snd ` Mapping.keys phis"
    and "\<forall>\<phi> \<in> Mapping.keys phis. b \<notin> set (the (Mapping.lookup phis \<phi>))"
    shows "Mapping.lookup m\<^sub>1 b = None \<or> Mapping.lookup m\<^sub>1 b = Some {}"
    using assms unfolding phi_equiv_mapping_def
    apply (auto split: option.splits if_splits)
    apply (clarsimp simp: keys_dom_lookup)
    apply (rename_tac n \<phi>_args)
    apply (erule_tac x="(n,b)" in ballE)
     prefer 2 apply auto[1]
    by (cases "Mapping.lookup m\<^sub>1 b"; auto)

  lemma keys_phis'_codem [simp]: "Mapping.keys (phis'_codem next next' (ssa.phiNodes_of)) = Mapping.keys phis - {next}"
    unfolding phis'_codem_def
  by (auto simp: keys_dom_lookup fun_upd_apply lookup_delete split: option.splits if_splits)

  lemma keys_phis'_codem':
    assumes "nodes_of_phis \<approx>\<^sub>\<phi> ssa.phiNodes_of" and "next \<in> Mapping.keys phis"
    shows "Mapping.keys (phis'_codem next next' nodes_of_phis) = Mapping.keys phis - {next}"
    using assms unfolding phis'_codem_def phi_equiv_mapping_def ssa.keys_phidefNodes [OF ssa.phis_finite]
  by (force split: option.splits if_splits simp: fold_update_conv fun_upd_apply keys_dom_lookup lookup_delete)

  lemma triv_phis'_correct:
    assumes "nodes_of_phis \<approx>\<^sub>\<phi> ssa.phiNodes_of" and "next \<in> Mapping.keys phis" and "ssa.trivial (snd next)"
    shows "uninst_code.triv_phis' (phis'_codem next (substitution_code next) nodes_of_phis) next (ssa.trivial_phis) nodes_of_phis = uninst_code.ssa.trivial_phis (phis'_codem next (substitution_code next) nodes_of_phis)"
  proof (rule set_eqI)
    note keys_phis'_codem' [OF assms(1,2), simp]
    fix \<phi>

    from assms(2) ssa.phis_in_\<alpha>n [of "fst next" "snd next"]
    have "ssa.redundant"
      unfolding ssa.redundant_def ssa.allVars_def ssa.allDefs_def ssa.phiDefs_def
      apply (cases "next")
      apply (rename_tac n v)
      apply (rule bexI)
       apply (rule assms(3))
      by (auto simp: keys_dom_lookup)

    then interpret step: CFG_SSA_step_code \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
      by unfold_locales

    let ?u_g = "usesOf uses"
    let ?p_g = "phis"

    show "\<phi> \<in> uninst_code.triv_phis' (phis'_codem next (substitution_code next) nodes_of_phis) next (ssa.trivial_phis) nodes_of_phis \<longleftrightarrow> \<phi> \<in> uninst_code.ssa.trivial_phis (phis'_codem next (substitution_code next) nodes_of_phis)"
    proof (cases "\<phi> = next")
      case True
      hence "\<phi> \<notin> uninst_code.triv_phis' (phis'_codem next (substitution_code next) nodes_of_phis) next (ssa.trivial_phis) nodes_of_phis"
        unfolding uninst_code.triv_phis'_def by (auto split: option.splits)
      moreover
      from True have "\<phi> \<notin> Mapping.keys (phis'_codem next (substitution_code next) nodes_of_phis)"
        unfolding phis'_codem_def
        by (transfer fixing: nodes_of_phis "next") (auto simp: fold_update_conv split: if_splits option.splits)
      hence "\<phi> \<notin> uninst_code.ssa.trivial_phis (phis'_codem next (substitution_code next) nodes_of_phis)"
        unfolding uninst_code.ssa.trivial_phis_def by simp
      ultimately show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "Mapping.lookup nodes_of_phis (snd next)")
        case None
        hence "uninst_code.triv_phis' (phis'_codem next (substitution_code next) nodes_of_phis) next (ssa.trivial_phis) nodes_of_phis = ssa.trivial_phis - {next}"
          unfolding uninst_code.triv_phis'_def by auto
        moreover from None
        have "uninst_code.ssa.trivial_phis (phis'_codem next (substitution_code next) nodes_of_phis) = ssa.trivial_phis - {next}"
          unfolding phis'_codem_def uninst_code.ssa.trivial_phis_def by (auto simp: lookup_delete)
        ultimately show ?thesis by simp
      next
        case [simp]: (Some nodes)
        from assms(2) have "snd next \<in> snd ` dom (Mapping.lookup phis)" by (auto simp: keys_dom_lookup)
        with assms(1) Some have "finite nodes" by (rule nodes_of_phis_finite)
        hence [simp]: "set (sorted_list_of_set nodes) = nodes" by simp
        obtain \<phi>_node \<phi>_val where [simp]: "\<phi> = (\<phi>_node, \<phi>_val)" by (cases \<phi>) auto
        show ?thesis
        proof (cases "\<phi> \<in> nodes")
          case False
          with `\<phi> \<noteq> next` have "\<phi> \<in> uninst_code.triv_phis' (phis'_codem next (substitution_code next) nodes_of_phis) next (ssa.trivial_phis) nodes_of_phis \<longleftrightarrow> \<phi> \<in> ssa.trivial_phis"
            unfolding uninst_code.triv_phis'_def by simp
          moreover

          from False `\<phi> \<noteq> next` have "... \<longleftrightarrow> \<phi> \<in> uninst_code.ssa.trivial_phis (phis'_codem next (substitution_code next) nodes_of_phis)"
            unfolding phis'_codem_def uninst_code.ssa.trivial_phis_def
            by (auto simp add: keys_dom_lookup dom_def lookup_delete)
          ultimately show ?thesis by simp
        next
          case True
          with assms(1,2) have "\<phi> \<in> Mapping.keys phis"
            unfolding phi_equiv_mapping_def apply clarsimp
            apply (clarsimp simp: keys_dom_lookup)
            by (erule_tac x="next" in ballE) (auto split: option.splits if_splits)

          then obtain \<phi>_args where [simp]: "Mapping.lookup phis (\<phi>_node, \<phi>_val) = Some \<phi>_args"
            unfolding keys_dom_lookup by auto
          hence [simp]: "ssa.phi \<phi>_val = Some \<phi>_args"
            by (rule ssa.phis_phi)

          from True `\<phi> \<noteq> next` have "\<phi> \<in> uninst_code.triv_phis' (phis'_codem next (substitution_code next) nodes_of_phis) next (ssa.trivial_phis) nodes_of_phis \<longleftrightarrow>
            \<phi> \<in> ssa.trivial_phis \<or> ssa.trivial_code (snd \<phi>) (the (Mapping.lookup (phis'_codem next (substitution_code next) nodes_of_phis) \<phi>))"
            unfolding uninst_code.triv_phis'_def by simp
          moreover

          from `\<phi> \<noteq> next` `\<phi> \<in> Mapping.keys phis` `next \<in> Mapping.keys phis`
          have [simp]: "\<phi>_val \<noteq> snd next"
            unfolding keys_dom_lookup
            by (cases "next", cases \<phi>) (auto dest: ssa.phis_disj)

          show ?thesis
          proof (cases "\<phi> \<in> ssa.trivial_phis")
            case True
            hence "ssa.trivial_code \<phi>_val \<phi>_args"
              unfolding ssa.trivial_phis_def by clarsimp
            hence "ssa.trivial_code \<phi>_val (map (substNext_code next) \<phi>_args)"
              apply (rule ssa.trivial_code_mapI)
               prefer 2
               apply (clarsimp simp: substNext_code_def)
              apply (clarsimp simp: substNext_code_def substitution_code_def)
              apply (erule_tac c="\<phi>_val" in equalityCE)
               prefer 2 apply simp
              apply clarsimp
              apply (subgoal_tac "ssa.isTrivialPhi \<phi>_val (snd next)")
               apply (subgoal_tac "ssa.isTrivialPhi (snd next) \<phi>_val")
                apply (blast dest: isTrivialPhi_asymmetric)
               using assms(3) `next \<in> Mapping.keys phis`
               apply (clarsimp simp: ssa.trivial_def keys_dom_lookup)
               apply (frule isTrivial_the_trivial [rotated 1, where v="snd next"])
                apply -
                apply (rule ssa.phis_phi [where n="fst next"])
                apply simp
               apply simp
              apply (thin_tac "\<phi>_val = v" for v)
              using `ssa.trivial_code \<phi>_val \<phi>_args`
              apply (clarsimp simp: ssa.trivial_code_def)
              by (erule the_trivial_SomeE) (auto simp: ssa.isTrivialPhi_def)
            with calculation True `\<phi> \<noteq> next` `\<phi> \<in> nodes` show ?thesis
              unfolding uninst_code.ssa.trivial_phis_def phis'_codem_def
              by (clarsimp simp: keys_dom_lookup substNext_code_alt_def)
          next
            case False
            with calculation `\<phi> \<noteq> next` `\<phi> \<in> Mapping.keys phis` True show ?thesis
              unfolding phis'_codem_def uninst_code.ssa.trivial_phis_def
              by (auto simp: keys_dom_lookup triv_phis'_def ssa.trivial_code_def)
          qed
        qed
      qed
    qed
  qed

  lemma nodes_of_phis'_correct:
  assumes "nodes_of_phis \<approx>\<^sub>\<phi> ssa.phiNodes_of"
    and "next \<in> Mapping.keys phis" and "ssa.trivial (snd next)"
  shows "(nodes_of_phis' next (substitution_code next) nodes_of_phis) \<approx>\<^sub>\<phi> (uninst_code.ssa.phiNodes_of (phis'_codem next (substitution_code next) nodes_of_phis))"
  proof -
    from assms(2) obtain next_args where lookup_next [simp]: "Mapping.lookup phis next = Some next_args"
      unfolding keys_dom_lookup by auto
    hence phi_next [simp]: "ssa.phi (snd next) = Some next_args"
      by -(rule ssa.phis_phi [where n="fst next"], simp)
    from assms(3) have in_next_args: "\<And>v. v \<in> set next_args \<Longrightarrow> v = snd next \<or> v = substitution_code next"
      unfolding ssa.trivial_def substitution_code_def
      apply clarsimp
      apply (subst(asm) isTrivial_the_trivial)
        apply (rule ssa.phis_phi [where n="fst next"])
        apply simp
       apply assumption
      by (auto simp: ssa.isTrivialPhi_def split: option.splits)
    from assms(2) have [dest!]: "\<And>x vs. Mapping.lookup phis (x, snd next) = Some vs \<Longrightarrow> x = fst next \<and> vs = next_args"
      by (auto simp add: keys_dom_lookup dest: ssa.phis_disj [where n'="fst next"])
    show ?thesis
    unfolding phi_equiv_mapping_def
    apply (subgoal_tac "finite (dom (Mapping.lookup (phis'_codem next (substitution_code next) nodes_of_phis)))")
     prefer 2
     apply (subst dom_phis'_codem)
      apply (rule nodes_of_phis_finite [OF assms(1)], assumption)
      using assms(2) [unfolded keys_dom_lookup]
      apply clarsimp
     apply (clarsimp simp: ssa.phis_finite split: option.splits)
     apply (rule nodes_of_phis_finite [OF assms(1)], assumption)
     using assms(2) [unfolded keys_dom_lookup]
     apply clarsimp
    unfolding phis'_codem_correct [OF assms(1,2)]
    apply (intro ballI)
    apply (rename_tac v)
    apply (subst(asm) ssa.keys_phidefNodes [OF ssa.phis_finite])
    apply (subst uninst_code.ssa.lookup_phiNodes_of, assumption)
    apply (subst lookup_phis'_code)+
    apply (subst substNext_code_def)+
    apply (subst dom_phis'_code)+
    apply (cases "\<exists>\<phi> \<in> Mapping.keys phis. snd next \<in> set (the (Mapping.lookup phis \<phi>))")
     apply (erule bexE)
     apply (subst(asm) keys_dom_lookup)
     apply (drule domD)
     apply (erule exE)
     apply (rule phi_equiv_mappingE [OF assms(1,2)], assumption)
      apply clarsimp
     apply (cases "substitution_code next \<in> snd ` Mapping.keys phis")
      apply (cases "\<exists>\<phi>' \<in> Mapping.keys phis. substitution_code next \<in> set (the (Mapping.lookup phis \<phi>'))")
       apply (erule bexE)
       apply (subst(asm) keys_dom_lookup)+
       apply (drule domD)
       apply (erule exE)
       apply (rule_tac x="\<phi>'" in phi_equiv_mappingE' [OF assms(1)], assumption)
         apply simp
        apply (simp add: keys_dom_lookup)
       apply (case_tac "v = substitution_code next")
        apply (simp only:)
        apply (subst lookup_nodes_of_phis'_subst)
        apply (simp add: lookup_phis'_code)
        apply (auto 4 4 intro: rev_image_eqI
          simp: keys_dom_lookup map_option_case substNext_code_def split: option.splits)[1]
       apply (subst lookup_nodes_of_phis'_not_subst, assumption)
       apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys phis. v \<in> set (the (Mapping.lookup phis \<phi>\<^sub>v))")
        apply (erule bexE)
        apply (simp add: keys_dom_lookup)
        apply (drule domD)
        apply (erule exE)
        apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
          apply simp
         apply (clarsimp simp: keys_dom_lookup)
        apply (clarsimp simp: keys_dom_lookup)
        apply (rename_tac n v \<phi>_args n' v' n'' \<phi>_args' \<phi>_args'')
        apply (auto dest: in_next_args)[1]
        apply (erule_tac x="(n,v)" in ballE)
         prefer 2 apply (auto dest: in_next_args)[1]
        apply auto[1]
       using phi_equiv_mappingE2' [OF assms(1), rotated 1]
       apply (erule_tac x=v in meta_allE)
       apply (erule meta_impE)
        apply clarsimp
       apply (auto simp: keys_dom_lookup)[1]
        apply force
       apply force
      using phi_equiv_mappingE2' [OF assms(1), rotated 1]
      apply (erule_tac x="substitution_code next" in meta_allE)
      apply (erule meta_impE)
       apply clarsimp
      apply (erule meta_impE)
       apply assumption
      apply (case_tac "v = substitution_code next")
       apply (auto simp: keys_dom_lookup)[1]
            apply force
           apply force
          apply force
         apply force
        apply force
       apply force
      apply (subst lookup_nodes_of_phis'_not_subst, assumption)
      apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys phis. v \<in> set (the (Mapping.lookup phis \<phi>\<^sub>v))")
       apply (erule bexE)
       apply (simp add: keys_dom_lookup)
       apply (drule domD)
       apply (erule exE)
       apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
         apply simp
        apply (clarsimp simp: keys_dom_lookup)
       apply (auto simp: keys_dom_lookup dest: in_next_args)[1]
        apply (force dest: in_next_args)[1]
       apply (force dest: in_next_args)[1]
      using phi_equiv_mappingE2' [OF assms(1), rotated 1]
      apply (erule_tac x=v in meta_allE)
      apply (erule meta_impE)
       apply clarsimp
      apply (auto simp: keys_dom_lookup)[1]
         apply force
        apply force
       apply force
      apply force
     apply (case_tac "v = substitution_code next")
      apply (auto simp: keys_dom_lookup)[1]
     apply (subst lookup_nodes_of_phis'_not_subst, assumption)
     apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys phis. v \<in> set (the (Mapping.lookup phis \<phi>\<^sub>v))")
      apply (erule bexE)
      apply (simp add: keys_dom_lookup)
      apply (drule domD)
      apply (erule exE)
      apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
        apply simp
       apply (clarsimp simp: keys_dom_lookup)
      apply (auto simp: keys_dom_lookup dest: in_next_args)[1]
      apply (force dest: in_next_args)[1]
     using phi_equiv_mappingE2' [OF assms(1), rotated 1]
     apply (erule_tac x="v" in meta_allE)
     apply (erule meta_impE)
      apply clarsimp
     apply (auto simp: keys_dom_lookup)[1]
      apply force
     apply force
    using phi_equiv_mappingE2' [OF assms(1), rotated 1]
    apply (erule_tac x="snd next" in meta_allE)
    apply (erule meta_impE)
     apply clarsimp
    apply (erule meta_impE)
     using assms(2)
     apply clarsimp
    apply (subgoal_tac "{n \<in> Mapping.keys phis. snd next \<in> set (the (Mapping.lookup phis n))} = {}")
     prefer 2
     apply auto[1]
    apply (cases "substitution_code next \<in> snd ` Mapping.keys phis")
     apply (cases "\<exists>\<phi>' \<in> Mapping.keys phis. substitution_code next \<in> set (the (Mapping.lookup phis \<phi>'))")
      apply (erule bexE)
      apply (subst(asm) keys_dom_lookup)+
      apply (drule domD)
      apply (erule exE)
      apply (rule_tac x="\<phi>'" in phi_equiv_mappingE' [OF assms(1)], assumption)
        apply simp
       apply (simp add: keys_dom_lookup)
      apply (case_tac "v = substitution_code next")
       apply (auto simp: keys_dom_lookup; force)[1]
      apply (subst lookup_nodes_of_phis'_not_subst, assumption)
      apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys phis. v \<in> set (the (Mapping.lookup phis \<phi>\<^sub>v))")
       apply (erule bexE)
       apply (simp add: keys_dom_lookup)
       apply (drule domD)
       apply (erule exE)
       apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
         apply simp
        apply (clarsimp simp: keys_dom_lookup)
       apply (auto simp: keys_dom_lookup dest: in_next_args)[1]
        apply (force dest: in_next_args)[1]
       apply (force dest: in_next_args)[1]
      using phi_equiv_mappingE2' [OF assms(1), rotated 1]
      apply (erule_tac x=v in meta_allE)
      apply (erule meta_impE)
       apply clarsimp
      apply (auto simp: keys_dom_lookup; force)[1]
     using phi_equiv_mappingE2' [OF assms(1), rotated 1]
     apply (erule_tac x="substitution_code next" in meta_allE)
     apply (erule meta_impE)
      apply clarsimp
     apply (erule meta_impE)
      apply assumption
     apply (case_tac "v = substitution_code next")
      apply (auto simp: keys_dom_lookup; force)[1]
     apply (subst lookup_nodes_of_phis'_not_subst, assumption)
     apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys phis. v \<in> set (the (Mapping.lookup phis \<phi>\<^sub>v))")
      apply (erule bexE)
      apply (simp add: keys_dom_lookup)
      apply (drule domD)
      apply (erule exE)
      apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
        apply simp
       apply (clarsimp simp: keys_dom_lookup)
      apply (auto simp: keys_dom_lookup dest: in_next_args; force dest: in_next_args)[1]
     using phi_equiv_mappingE2' [OF assms(1), rotated 1]
     apply (erule_tac x="v" in meta_allE)
     apply (erule meta_impE)
      apply clarsimp
     apply (erule meta_impE)
      apply (clarsimp simp: keys_dom_lookup)
     apply (auto simp: keys_dom_lookup; force)[1]
    apply (case_tac "v = substitution_code next")
     apply (auto simp: keys_dom_lookup)[1]
    apply (subst lookup_nodes_of_phis'_not_subst, assumption)
    apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys phis. v \<in> set (the (Mapping.lookup phis \<phi>\<^sub>v))")
     apply (erule bexE)
     apply (simp add: keys_dom_lookup)
     apply (drule domD)
     apply (erule exE)
     apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
       apply simp
      apply (clarsimp simp: keys_dom_lookup)
     apply (auto simp: keys_dom_lookup dest: in_next_args; force dest: in_next_args)[1]
    using phi_equiv_mappingE2' [OF assms(1), rotated 1]
    apply (erule_tac x=v in meta_allE)
    apply (erule meta_impE)
     apply clarsimp
    apply (erule meta_impE)
     apply (clarsimp simp: keys_dom_lookup)
    apply (auto simp: keys_dom_lookup; force)[1]
    done
  qed



  lemma nodes_of_uses'_correct:
  assumes "nodes_of_uses \<approx>\<^sub>\<phi> ssa.useNodes_of"
    and "next \<in> Mapping.keys phis" and "ssa.trivial (snd next)"
  shows "(nodes_of_uses' next (substitution_code next) (Mapping.keys (ssa.phidefNodes)) nodes_of_uses) \<approx>\<^sub>\<phi> (uninst_code.ssa.useNodes_of (uses'_codem next (substitution_code next) nodes_of_uses))"
  proof -
    from assms(2,3) ssa.phis_in_\<alpha>n [of "fst next" "snd next"]
    have "ssa.redundant"
      unfolding ssa.redundant_def ssa.allVars_def ssa.allDefs_def ssa.phiDefs_def
      apply -
      apply (rule bexI, assumption)
      by (cases "next") (auto simp: keys_dom_lookup)

    then interpret step: CFG_SSA_step_code \<alpha>n predecessors Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
      by unfold_locales


    from assms(2,3) obtain next_args v where lookup_next [simp]: "Mapping.lookup phis next = Some next_args"
      and "ssa.isTrivialPhi (snd next) v"
      unfolding keys_dom_lookup ssa.trivial_def by auto
    hence phi_next [simp]: "ssa.phi (snd next) = Some next_args"
      by -(rule ssa.phis_phi [where n="fst next"], simp)
    hence the_trivial_next_args [simp]: "the_trivial (snd next) next_args = Some v" using `ssa.isTrivialPhi (snd next) v`
      by (rule isTrivial_the_trivial)

    from assms(3) have in_next_args: "\<And>v. v \<in> set next_args \<Longrightarrow> v = snd next \<or> v = substitution_code next"
      unfolding ssa.trivial_def substitution_code_def
      apply (clarsimp simp del: the_trivial_next_args)
      apply (subst(asm) isTrivial_the_trivial)
        apply (rule ssa.phis_phi [where n="fst next"])
        apply simp
       apply assumption
      by (auto simp: ssa.isTrivialPhi_def split: option.splits)

    from `ssa.isTrivialPhi (snd next) v`
    have triv_phi_is_v [dest!]: "\<And>v'. ssa.isTrivialPhi (snd next) v' \<Longrightarrow> v' = v"
      using isTrivialPhi_det [OF assms(3)] by auto

    from `ssa.isTrivialPhi (snd next) v` have [simp]: "v \<noteq> snd next" unfolding ssa.isTrivialPhi_def by simp

    from assms(2) have [dest]: "\<And>x vs. Mapping.lookup phis (x, snd next) = Some vs \<Longrightarrow> x = fst next \<and> vs = next_args"
      by (auto simp add: keys_dom_lookup dest: ssa.phis_disj [where n'="fst next"])

    have substNext_idem [simp]: "\<And>v. substNext (substNext v) = substNext v"
      unfolding substNext_def by (auto split: if_splits)

    from assms(1)
    have nodes_of_uses_eq_NoneD [elim_format, elim]: "\<And>v n args. \<lbrakk>Mapping.lookup nodes_of_uses v = None; Mapping.lookup phis (n,v) = Some args \<rbrakk>
      \<Longrightarrow> (\<forall>n \<in> set \<alpha>n. \<forall>vs. Mapping.lookup uses n = Some vs \<longrightarrow> v \<notin> vs)"
       unfolding phi_equiv_mapping_def
     apply (clarsimp simp: ssa.lookup_useNodes_of split: option.splits if_splits)
     by (erule_tac x="(n,v)" in ballE) auto

    from assms(1)
    have nodes_of_uses_eq_SomeD [elim_format, elim]: "\<And>v nodes n args. \<lbrakk> Mapping.lookup nodes_of_uses v = Some nodes; Mapping.lookup phis (n,v) = Some args\<rbrakk>
      \<Longrightarrow> nodes = {n \<in> set \<alpha>n. \<exists>vs. Mapping.lookup uses n = Some vs \<and> v \<in> vs}"
      unfolding phi_equiv_mapping_def
    apply (clarsimp simp: ssa.lookup_useNodes_of split: option.splits if_splits)
    by (erule_tac x="(n,v)" in ballE) auto

    show ?thesis
    unfolding phi_equiv_mapping_def nodes_of_uses'_def substitution_code_def Let_def ssa.keys_phidefNodes [OF ssa.phis_finite]
    apply (subst uses'_codem_correct [OF assms(1,2), unfolded substitution_code_def])
    apply (subst uninst.lookup_useNodes_of')
     apply (clarsimp simp: uses'_code_def split: option.splits)
     apply (rule finite_imageI)
     using ssa.uses_finite [of]
     apply (fastforce split: option.splits)[1]
    apply (cases "v \<in> snd ` dom (Mapping.lookup phis)")
     prefer 2
     apply (auto 4 3 simp: lookup_delete uninst_code.uses'_code_def substNext_code_def substitution_code_def
       split: option.splits
       intro: rev_image_eqI; fail)[1]
    apply (clarsimp simp: Mapping_lookup_map_default lookup_delete uses'_code_def substNext_code_def substitution_code_def)
    apply (rename_tac n n' v' phi_args phi_args')
    apply safe
                         apply (auto elim: nodes_of_uses_eq_SomeD [where n="fst next"]
                           nodes_of_uses_eq_NoneD [where n="fst next"] simp: phi_equiv_mapping_def split: option.splits)[13]

            using assms(1)
            apply (simp add: phi_equiv_mapping_def)
            apply (erule_tac x="(n,v)" in ballE)
             prefer 2 apply auto[1]
            apply (auto simp: ssa.lookup_useNodes_of split: option.splits)[1]

           apply (auto elim: nodes_of_uses_eq_SomeD [where n="fst next"]
             nodes_of_uses_eq_NoneD [where n="fst next"] split: option.splits)[1]

          using assms(1)
          apply (simp add: phi_equiv_mapping_def)
          apply (erule_tac x="(n,v)" in ballE)
           prefer 2 apply auto[1]
          apply (auto simp: ssa.lookup_useNodes_of split: option.splits)[1]

         apply (auto 4 3 elim: nodes_of_uses_eq_SomeD [where n="fst next"] split: option.splits)[4]

     using assms(1)
     apply (simp add: phi_equiv_mapping_def)
     apply (erule_tac x="(n',v')" in ballE)
      prefer 2 apply auto[1]
     apply (auto simp: ssa.lookup_useNodes_of split: option.splits)[1]

    by (auto split: option.splits)[1]
  qed

  definition[code]: "substAll_efficient \<equiv>
    let phiVals = Mapping.keys (ssa.phidefNodes);
        u = uses;
        p = phis;
        tp = ssa.trivial_phis;
        nou = ssa.useNodes_of;
        nop = ssa.phiNodes_of
    in
    while
    (\<lambda>((u,p),triv_phis,nodes_of_uses,nodes_of_phis). \<not> Set.is_empty triv_phis)
    (\<lambda>((u,p),triv_phis,nodes_of_uses,nodes_of_phis). let
        next = Max triv_phis;
        next' = uninst_code.substitution_code p next;
        (u',p') = uninst_code.step_codem u p next next' nodes_of_uses nodes_of_phis;
        tp' = uninst_code.triv_phis' p' next triv_phis nodes_of_phis;
        nou' = uninst_code.nodes_of_uses' next next' phiVals nodes_of_uses;
        nop' = uninst_code.nodes_of_phis' next next' nodes_of_phis
      in ((u', p'), tp', nou', nop'))
    ((u, p), tp, nou, nop)"

  abbreviation "u_c x \<equiv> usesOf (fst x)"
  abbreviation "p_c x \<equiv> Mapping.lookup (snd x)"
  abbreviation "u x \<equiv> fst x"
  abbreviation "p x \<equiv> snd x"

  lemma keys_uses'_codem [simp]: "Mapping.keys (uses'_codem next (substitution_code next) (ssa.useNodes_of)) = Mapping.keys uses"
    unfolding uses'_codem_def
  apply (transfer fixing:)
  apply (auto split: option.splits if_splits simp: fold_update_conv)
  by (subst(asm) sorted_list_of_set) (auto intro: finite_subset [OF _ finite_set])

  lemma keys_uses'_codem': "\<lbrakk> nodes_of_uses \<approx>\<^sub>\<phi> ssa.useNodes_of; next \<in> Mapping.keys phis \<rbrakk>
    \<Longrightarrow> Mapping.keys (uses'_codem next (substitution_code next) nodes_of_uses) = Mapping.keys uses"
    unfolding uses'_codem_def
  apply (clarsimp simp: keys_dom_lookup split: if_splits option.splits)
  apply (auto simp: phi_equiv_mapping_def)
  by (erule_tac x="next" in ballE) (auto simp: ssa.lookup_useNodes_of split: if_splits option.splits)

  lemma phi_equiv_mapping_refl [simp]: "uninst_code.phi_equiv_mapping ph m m"
    unfolding uninst_code.phi_equiv_mapping_def by simp

  lemma substAll_efficient_code [code]:
    "substAll = map_prod usesOf Mapping.lookup (fst (substAll_efficient))"
    unfolding substAll_efficient_def while_def substAll_def Let_def
  apply -
  apply (rule map_option_the [OF _ substAll_terminates])
  proof (rule while_option_sim [where
      R="\<lambda>x y. y = map_option (\<lambda>a. map_prod usesOf Mapping.lookup (fst (f a))) x" and
      I="\<lambda>((u,p),triv_phis,nodes_of_uses, phis_of_nodes). Mapping.keys u \<subseteq> set \<alpha>n \<and> Mapping.keys p \<subseteq> Mapping.keys phis
        \<and> CFG_SSA_Transformed_notriv_linorder_code \<alpha>n predecessors Entry oldDefs oldUses defs u p var chooseNext_all
        \<and> triv_phis = uninst_code.ssa.trivial_phis p
        \<and> uninst_code.phi_equiv_mapping p nodes_of_uses (uninst_code.ssa.useNodes_of u)
        \<and> uninst_code.phi_equiv_mapping p phis_of_nodes (uninst_code.ssa.phiNodes_of p)"
      for f
      , simplified], simp_all add: split_def dom_uses_in_graph Set.is_empty_def)
    show "CFG_SSA_Transformed_notriv_linorder_code \<alpha>n predecessors Entry oldDefs oldUses defs uses phis var
     chooseNext_all"
      by unfold_locales
  next
    fix s1
    assume "Mapping.keys (fst (fst s1)) \<subseteq> set \<alpha>n \<and> Mapping.keys (snd (fst s1)) \<subseteq> Mapping.keys phis
      \<and> CFG_SSA_Transformed_notriv_linorder_code \<alpha>n predecessors Entry oldDefs oldUses defs (u (fst s1)) (p (fst s1)) var chooseNext_all
      \<and> fst (snd s1) = uninst_code.ssa.trivial_phis (snd (fst s1))
      \<and> uninst_code.phi_equiv_mapping (snd (fst s1)) (fst (snd (snd s1))) (uninst_code.ssa.useNodes_of (fst (fst s1)))
      \<and> uninst_code.phi_equiv_mapping (snd (fst s1)) (snd (snd (snd s1))) (uninst_code.ssa.phiNodes_of (snd (fst s1)))"
    then obtain s1_uses s1_phis s1_triv_phis s1_nodes_of_uses s1_phi_nodes_of where
      s1_def [simp]: "s1 = ((s1_uses, s1_phis), s1_triv_phis, s1_nodes_of_uses, s1_phi_nodes_of)"
      and "Mapping.keys s1_uses \<subseteq> set \<alpha>n"
      and "Mapping.keys s1_phis \<subseteq> Mapping.keys phis"
      and "CFG_SSA_Transformed_notriv_linorder_code \<alpha>n predecessors Entry oldDefs oldUses defs s1_uses s1_phis var chooseNext_all"
      and [simp]: "s1_triv_phis = uninst_code.ssa.trivial_phis s1_phis"
      and nou_equiv: "uninst_code.phi_equiv_mapping s1_phis s1_nodes_of_uses (uninst_code.ssa.useNodes_of s1_uses)"
      and pno_equiv: "uninst_code.phi_equiv_mapping s1_phis s1_phi_nodes_of (uninst_code.ssa.phiNodes_of s1_phis)"
      by (cases s1; auto)
    from this(4) interpret i: CFG_SSA_Transformed_notriv_linorder_code \<alpha>n predecessors Entry oldDefs oldUses "defs" s1_uses s1_phis var chooseNext_all .
    let ?s2 = "map_prod usesOf Mapping.lookup (fst s1)"
    have [simp]: "uninst_code.ssa.trivial_phis s1_phis \<noteq> {} \<longleftrightarrow> cond ?s2"
      unfolding uninst_code.ssa.redundant_code_def [symmetric]
      by (clarsimp simp add: cond_def i.ssa.redundant_code [simplified, symmetric])
    thus "uninst_code.ssa.trivial_phis (snd (fst s1)) \<noteq> {} \<longleftrightarrow> cond ?s2"
      by simp
    {
      assume "uninst_code.ssa.trivial_phis (snd (fst s1)) \<noteq> {}"
      hence red: "uninst.redundant (usesOf s1_uses) (Mapping.lookup s1_phis)"
        by (simp add: cond_def uninst.CFG_SSA_wf_defs)
      then interpret step: CFG_SSA_step_code \<alpha>n predecessors Entry oldDefs oldUses "defs"
        s1_uses s1_phis var chooseNext_all
        by unfold_locales simp
      from step.step_CFG_SSA_Transformed_notriv[simplified]
      interpret step_step: CFG_SSA_Transformed_notriv \<alpha>n predecessors Entry oldDefs oldUses "defs"
      "uninst.uses' (usesOf s1_uses) (Mapping.lookup s1_phis)"
      "uninst.phis' (usesOf s1_uses) (Mapping.lookup s1_phis)"
      var i.cN .

      interpret step_step: CFG_SSA_ext \<alpha>n predecessors Entry "defs"
      "uninst.uses' (usesOf s1_uses) (Mapping.lookup s1_phis)"
      "uninst.phis' (usesOf s1_uses) (Mapping.lookup s1_phis)"
      ..

      from `Mapping.keys s1_uses \<subseteq> set \<alpha>n`
      have keys_u_g: "Mapping.keys (s1_uses) \<subseteq> set \<alpha>n"
        by clarsimp

      have i_cN [simp]: "Max (CFG_SSA_wf_base_code.trivial_phis (s1_phis)) = chooseNext_all (usesOf (s1_uses)) (s1_phis)"
      apply (rule chooseNext_all_code [where u="s1_uses", symmetric])
      by unfold_locales (simp add: i.ssa.redundant_code [symmetric])

      have [simp]: "chooseNext_all (usesOf s1_uses) s1_phis \<in> Mapping.keys s1_phis"
        using i.chooseNext'
        by (clarsimp simp: Mapping.keys_dom_lookup)

      from `Mapping.keys s1_phis \<subseteq> Mapping.keys phis`
      have "finite (Mapping.keys s1_phis)"
      by (rule finite_subset) (auto simp: keys_dom_lookup intro: ssa.phis_finite)

      have uses_conv: "(usesOf
           (CFG_SSA_Transformed_notriv_base_code.uses'_codem (s1_uses)
             (chooseNext_all (usesOf s1_uses) s1_phis)
             (uninst_code.substitution_code (s1_phis) (chooseNext_all (usesOf s1_uses) s1_phis))
             s1_nodes_of_uses))
                  = CFG_SSA_Transformed_notriv_base.uses' \<alpha>n defs (usesOf s1_uses) ( Mapping.lookup (s1_phis))
              i.cN"
       unfolding i.uses'_code_correct [OF red]
       apply (subst i.uses'_codem_correct [symmetric, where nodes_of_uses=s1_nodes_of_uses])
         apply (rule nou_equiv [simplified])
        apply auto[1]
       by (auto simp: fun_upd_apply)

      have phis_conv: "Mapping.lookup
                (CFG_SSA_Transformed_notriv_base_code.phis'_codem (s1_phis)
                         (chooseNext_all (usesOf s1_uses) s1_phis)
                         (uninst_code.substitution_code (s1_phis) (chooseNext_all (usesOf s1_uses) s1_phis))
                         (CFG_SSA_base.phiNodes_of (Mapping.lookup (s1_phis))))
                   =
       CFG_SSA_Transformed_notriv_base.phis' \<alpha>n defs (usesOf s1_uses) (Mapping.lookup (s1_phis))
              i.cN"
       apply (subst i.phis'_code_correct [OF red])
       apply (subst i.phis'_codem_correct [symmetric])
       by (auto simp: fun_upd_apply)

      let ?next = "Max (uninst_code.ssa.trivial_phis ((snd (fst s1))))"
      let ?u' = "fst (uninst_code.step_codem (u (fst s1)) (p (fst s1)) ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) (fst (snd (snd s1))) (snd (snd (snd s1))))"
      let ?p' = "snd (uninst_code.step_codem (u (fst s1)) (p (fst s1)) ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) (fst (snd (snd s1))) (snd (snd (snd s1))))"

      show step_s2: "step ?s2 = map_prod usesOf Mapping.lookup (uninst_code.step_codem (u (fst s1)) (p (fst s1))
        ?next (uninst_code.substitution_code ((snd (fst s1))) ?next)
        (fst (snd (snd s1))) (snd (snd (snd s1))))"
        unfolding uninst_code.step_codem_def uninst.step_def split_def map_prod_def Let_def
      by (auto simp: map_prod_def Let_def step_step.usesOf_cache[simplified]
        i.phis'_codem_correct [OF pno_equiv [simplified]]
        i.phis'_code_correct[simplified, symmetric]
        i.uses'_codem_correct [OF nou_equiv [simplified]]
        i.uses'_code_correct [OF red, symmetric, simplified])

      have [simplified, simp]:
        "uninst_code.phis'_codem (p (fst s1)) ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) s1_phi_nodes_of
          = uninst_code.phis'_codem (p (fst s1)) ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) (uninst_code.ssa.phiNodes_of ((snd (fst s1))))"
        by (auto simp: i.phis'_codem_correct [OF phi_equiv_mapping_refl] i.phis'_codem_correct [OF pno_equiv [simplified]])

      have [simplified, simp]:
        "usesOf (uninst_code.uses'_codem (u (fst s1)) ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) s1_nodes_of_uses)
          = usesOf (uninst_code.uses'_codem (u (fst s1)) ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) (uninst_code.ssa.useNodes_of ((fst (fst s1)))))"
        by (auto simp: i.uses'_codem_correct [OF phi_equiv_mapping_refl] i.uses'_codem_correct [OF nou_equiv [simplified]])

      from step_s2[symmetric] step.step_CFG_SSA_Transformed_notriv `Mapping.keys s1_uses \<subseteq> set \<alpha>n`
        `Mapping.keys s1_phis \<subseteq> Mapping.keys phis`
      have "Mapping.keys ?u' \<subseteq> set \<alpha>n \<and>
          Mapping.keys ?p' \<subseteq> Mapping.keys phis \<and>
          CFG_SSA_Transformed_notriv_linorder_code \<alpha>n predecessors Entry oldDefs oldUses defs
           (u (uninst_code.step_codem (u (fst s1)) (p (fst s1)) ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) s1_nodes_of_uses s1_phi_nodes_of))
           (p (uninst_code.step_codem (u (fst s1)) (p (fst s1)) ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) s1_nodes_of_uses s1_phi_nodes_of))
           var chooseNext_all"
      unfolding CFG_SSA_Transformed_notriv_linorder_code_def
        CFG_SSA_Transformed_notriv_linorder_def
        CFG_SSA_Transformed_code_def
        CFG_SSA_wf_code_def CFG_SSA_code_def
      apply (clarsimp simp: map_prod_def split_def uninst_code.step_codem_def Let_def uses_conv [simplified] phis_conv)
      apply (rule conjI)
       prefer 2
       apply (rule conjI)
        prefer 2
        apply (intro conjI; unfold_locales)
         by (auto intro!: dom_uses_in_graph chooseNext_all_code
           simp: fun_upd_apply
             i.keys_phis'_codem' [OF pno_equiv [simplified], of ?next, simplified fun_upd_apply, simplified]
             i.keys_uses'_codem' [OF nou_equiv [simplified], of ?next, simplified fun_upd_apply, simplified])
      moreover

      from i.triv_phis'_correct [of "snd (snd (snd s1))" ?next] i.chooseNext' [of]
      have "uninst_code.triv_phis' (?p') ?next s1_triv_phis (snd (snd (snd s1)))
        = uninst_code.ssa.trivial_phis (?p')"
        by (auto intro: pno_equiv [simplified] simp: uninst_code.step_codem_def)
      moreover

      from `Mapping.keys s1_phis \<subseteq> Mapping.keys phis` ssa.phis_finite
      have "finite (dom (Mapping.lookup s1_phis))"
        by (auto intro: finite_subset simp: keys_dom_lookup)
      hence phi_equiv_mapping_p'I [simplified]:
      "\<And>m1 m2. uninst_code.phi_equiv_mapping (s1_phis) m1 m2 \<Longrightarrow> uninst_code.phi_equiv_mapping (?p') m1 m2"
        unfolding uninst_code.phi_equiv_mapping_def
        apply clarsimp
        apply (subst(asm) uninst.keys_phidefNodes)
         apply (simp add: uninst_code.step_codem_def keys_dom_lookup [symmetric])
        by (clarsimp simp: uninst_code.step_codem_def keys_dom_lookup [symmetric]) fastforce

      have "?next \<in> Mapping.keys s1_phis" by auto
      with `Mapping.keys s1_phis \<subseteq> Mapping.keys phis` nou_equiv i.chooseNext' [of]
      have "uninst_code.nodes_of_uses' ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) (snd ` dom (Mapping.lookup phis)) (fst (snd (snd s1)))
        = uninst_code.nodes_of_uses' ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) (snd ` dom (Mapping.lookup s1_phis)) (fst (snd (snd s1)))"
        unfolding uninst_code.nodes_of_uses'_def
        apply -
        apply (erule meta_impE)
         apply auto[1]
        apply (auto simp: Let_def uninst_code.substitution_code_def keys_dom_lookup uninst_code.ssa.trivial_def)
        apply (drule i.isTrivial_the_trivial [rotated 1])
         apply (rule i.ssa.phis_phi [where n="fst ?next"])
         apply simp
        apply clarsimp
        apply (drule i.ssa.allVars_in_allDefs)
        apply clarsimp
        apply (drule ssa.phis_phi)
        apply clarsimp
        apply (clarsimp simp: uninst_code.ssa.allVars_def uninst_code.ssa.allDefs_def uninst_code.ssa.allUses_def uninst_code.ssa.phiDefs_def)
        apply (erule disjE)
         apply (drule(1) ssa.simpleDef_not_phi)
         apply simp
        by (auto intro: rev_image_eqI)

      ultimately
      show "Mapping.keys ?u' \<subseteq> set \<alpha>n \<and>
          Mapping.keys ?p' \<subseteq> Mapping.keys phis \<and>
          CFG_SSA_Transformed_notriv_linorder_code \<alpha>n predecessors Entry oldDefs oldUses defs
           (u (uninst_code.step_codem (u (fst s1)) (p (fst s1)) (Max (uninst_code.ssa.trivial_phis ((snd (fst s1))))) (uninst_code.substitution_code ((snd (fst s1))) ?next) (fst (snd (snd s1))) (snd (snd (snd s1)))))
           (p (uninst_code.step_codem (u (fst s1)) (p (fst s1)) (Max (uninst_code.ssa.trivial_phis ((snd (fst s1))))) (uninst_code.substitution_code ((snd (fst s1))) ?next) (fst (snd (snd s1))) (snd (snd (snd s1)))))
           var chooseNext_all \<and>
          uninst_code.triv_phis' (?p') ?next (uninst_code.ssa.trivial_phis ((snd (fst s1)))) (snd (snd (snd s1)))
            = uninst_code.ssa.trivial_phis (?p') \<and>
          uninst_code.phi_equiv_mapping (?p') (uninst_code.nodes_of_uses' ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) (snd ` dom (Mapping.lookup phis)) (fst (snd (snd s1)))) (uninst_code.ssa.useNodes_of (?u')) \<and>
          uninst_code.phi_equiv_mapping (?p') (uninst_code.nodes_of_phis' ?next (uninst_code.substitution_code ((snd (fst s1))) ?next) (snd (snd (snd s1)))) (uninst_code.ssa.phiNodes_of (?p'))"
      using i.nodes_of_uses'_correct [of s1_nodes_of_uses ?next, OF nou_equiv [simplified]]
        i.chooseNext' [of]
        i.nodes_of_phis'_correct [of s1_phi_nodes_of ?next, OF pno_equiv [simplified]]
        apply simp
        apply (rule conjI)
         apply (rule phi_equiv_mapping_p'I)
         apply (clarsimp simp: uninst_code.step_codem_def)
        apply (rule phi_equiv_mapping_p'I)
        by (clarsimp simp: uninst_code.step_codem_def)
    }
  qed

end

end
