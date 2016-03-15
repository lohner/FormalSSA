(*  Title:      WhileGraphSSA.thy
    Author:     Denis Lohner, Sebastian Ullrich
*)

subsubsection {* Instantiation for a Simple While Language *}

theory WhileGraphSSA imports
SingleInstruction_CFG
"$AFP/Slicing/While/AdditionalLemmas"
"~~/src/HOL/Library/List_lexord"
"~~/src/HOL/Library/Char_ord"
begin

instantiation w_node :: ord
begin

fun less_eq_w_node where
  "(_Entry_) \<le> x = True"
| "(_ n _) \<le> x = (case x of
     (_Entry_) \<Rightarrow> False
   | (_ m _) \<Rightarrow> n \<le> m
   | (_Exit_) \<Rightarrow> True)"
| "(_Exit_) \<le> x = (x = (_Exit_))"

fun less_w_node where
  "(_Entry_) < x = (x \<noteq> (_Entry_))"
| "(_ n _) < x = (case x of
     (_Entry_) \<Rightarrow> False
   | (_ m _) \<Rightarrow> n < m
   | (_Exit_) \<Rightarrow> True)"
| "(_Exit_) < x = False"

instance ..
end

instance w_node :: linorder proof
  fix x y z :: w_node

  show "x \<le> x" by (cases x) auto
  show "x \<le> y \<or> y \<le> x" by (cases x) (cases y, auto)+
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (cases x) (cases y, auto)+

  assume "x \<le> y" and "y \<le> z"
  thus "x \<le> z" by (cases x, cases y, cases z) auto

  assume "x \<le> y" and "y \<le> x"
  thus "x = y" by (cases x) (cases y, auto)+
qed

declare Defs.simps [simp del]
declare Uses.simps [simp del]
declare Let_def [simp]

declare finite_valid_nodes [simp, intro!]

lemma finite_valid_edge [simp, intro!]: "finite (Collect (valid_edge c))"
  unfolding valid_edge_def [abs_def]
apply (rule inj_on_finite [where f="\<lambda>(f,d,t). (f,t)" and B="Collect (valid_node c) \<times> Collect (valid_node c)"])
  apply (rule inj_onI)
  apply (auto intro: WCFG_edge_det)[1]
 apply (force simp: valid_node_def valid_edge_def)[1]
by auto

lemma uses_expr_finite: "finite (rhs_aux e)"
  by (induction e) auto

lemma uses_cmd_finite: "finite (rhs c)"
  by (induction c) (auto intro: uses_expr_finite)

lemma defs_cmd_finite: "finite (lhs c)"
  by (induction c) auto

lemma finite_labels': "finite {(l,c). labels prog l c}"
proof -
  have "{l. \<exists>c. labels prog l c} = fst ` {(l,c). labels prog l c}"
    by auto
  with finite_labels [of prog] labels_det [of prog] show ?thesis
    by (auto 4 4 intro: inj_onI dest: finite_imageD)
qed

lemma finite_Defs [simp, intro!]: "finite (Defs c n)"
  unfolding Defs.simps
apply clarsimp
apply (rule_tac B="\<Union>(lhs ` snd ` {(l,c'). labels c l c'})" in finite_subset)
 apply fastforce
apply (rule finite_Union)
 apply (rule finite_imageI)+
 apply (rule finite_labels')
by (clarsimp simp: defs_cmd_finite)

lemma finite_Uses [simp, intro!]: "finite (Uses c n)"
  unfolding Uses.simps
apply clarsimp
apply (rule_tac B="\<Union>(rhs ` snd ` {(l,c'). labels c l c'})" in finite_subset)
 apply fastforce
apply (rule finite_Union)
 apply (rule finite_imageI)+
 apply (rule finite_labels')
by (clarsimp simp: uses_cmd_finite)

definition "while_cfg_\<alpha>e c = Collect (valid_edge c)"
definition "while_cfg_\<alpha>n c = sorted_list_of_set (Collect (valid_node c))"
definition "while_cfg_predecessors c t = (SOME ls. distinct ls \<and> set ls = {sourcenode e| e. valid_edge c e \<and> targetnode e = t})"
definition "while_cfg_Entry c = (_Entry_)"
definition "while_cfg_defs c = (Defs c)((_Entry_) := {v. \<exists>n. v \<in> Uses c n})"
definition "while_cfg_uses c = Uses c"

abbreviation "while_cfg_inEdges c t \<equiv> map (\<lambda>f. (f,(),t)) (while_cfg_predecessors c t)"

lemmas while_cfg_defs = while_cfg_\<alpha>e_def while_cfg_\<alpha>n_def
  while_cfg_predecessors_def
  while_cfg_Entry_def while_cfg_defs_def
  while_cfg_uses_def

interpretation while: graph_path "while_cfg_\<alpha>n c" "while_cfg_predecessors c"
  for c :: cmd
apply unfold_locales
apply (simp_all add: while_cfg_defs graph_path_base.\<alpha>e_def)[5]
    apply (rule finite_subset [OF _ finite_imageI [OF finite_valid_edge [of "c"], where h="\<lambda>(f,d,t). (f,(),t)"]])
    apply clarsimp
    using sorted_list_of_set [of "{n. \<exists>a. valid_edge c (n, a, m)}" for m]
    apply (erule_tac x=m in meta_allE)
    apply (erule meta_impE)
     apply (rule finite_subset [OF _ finite_valid_nodes [of "c"]])
     apply (fastforce simp: valid_node_def)
    apply (case_tac "n \<in> {n. \<exists>a. valid_edge c (n, a, m)}")
     prefer 2
     apply clarsimp
     apply (subgoal_tac "n \<notin> set (SOME ls. distinct ls \<and> set ls = {n. \<exists>a. valid_edge c (n, a, m)})")
      apply simp
     apply (rule_tac a="sorted_list_of_set {n. \<exists>a. valid_edge c (n, a, m)}" in someI2)
      using sorted_list_of_set [of "{n. \<exists>a. valid_edge c (n, a, m)}" for m]
      apply (erule_tac x=m in meta_allE)
      apply (erule meta_impE)
       apply (rule finite_subset [OF _ finite_valid_nodes [of "c"]])
       apply (fastforce simp: valid_node_def)
      apply simp
     apply fastforce
    apply (fastforce intro: rev_image_eqI)
   apply clarsimp
   apply (case_tac "n \<in> {n. \<exists>a. valid_edge c (n, a, m)}")
    prefer 2
    apply clarsimp
    apply (subgoal_tac "n \<notin> set (SOME ls. distinct ls \<and> set ls = {n. \<exists>a. valid_edge c (n, a, m)})")
     apply simp
    apply (rule_tac a="sorted_list_of_set {n. \<exists>a. valid_edge c (n, a, m)}" in someI2)
     using sorted_list_of_set [of "{n. \<exists>a. valid_edge c (n, a, m)}" for m]
     apply (erule_tac x=m in meta_allE)
     apply (erule meta_impE)
      apply (rule finite_subset [OF _ finite_valid_nodes [of "c"]])
      apply (fastforce simp: valid_node_def)
     apply simp
    apply fastforce
   apply (fastforce simp: valid_node_def)
  apply clarsimp
  apply (case_tac "n \<in> {n. \<exists>a. valid_edge c (n, a, m)}")
   prefer 2
   apply clarsimp
   apply (subgoal_tac "n \<notin> set (SOME ls. distinct ls \<and> set ls = {n. \<exists>a. valid_edge c (n, a, m)})")
    apply simp
   apply (rule_tac a="sorted_list_of_set {n. \<exists>a. valid_edge c (n, a, m)}" in someI2)
    using sorted_list_of_set [of "{n. \<exists>a. valid_edge c (n, a, m)}" for m]
    apply (erule_tac x=m in meta_allE)
    apply (erule meta_impE)
     apply (rule finite_subset [OF _ finite_valid_nodes [of "c"]])
     apply (fastforce simp: valid_node_def)
    apply simp
   apply fastforce
  apply (fastforce simp: valid_node_def)
 apply (rule set_iterator_I)
   prefer 3 apply (simp add: foldri_def)
  apply simp
 apply simp
apply (clarsimp simp: Graph_path.pred_def graph_path_base_base.inEdges_def)
apply (subgoal_tac "{(v', w). (v', (), v) \<in> graph_path_base.\<alpha>e (while_cfg_predecessors c)}
  = set (map (\<lambda>m. (m, ())) (while_cfg_predecessors c v))")
 apply (simp only:)
 apply (rule set_iterator_foldri_correct)
 apply (clarsimp simp: while_cfg_predecessors_def distinct_map)
 using sorted_list_of_set [of "{n. \<exists>a. valid_edge c (n, a, v)}" for v]
 apply (erule_tac x=v in meta_allE)
 apply (erule meta_impE)
  apply (rule finite_subset [OF _ finite_valid_nodes [of "c"]])
  apply (fastforce simp: valid_node_def)
 apply (rule someI2 [where a="sorted_list_of_set {n. \<exists>a. valid_edge c (n, a, v)}" for v])
  apply fastforce
 apply simp
by (auto simp: graph_path_base.\<alpha>e_def)

definition "gen_while_cfg c \<equiv> \<lparr>
  gen_\<alpha>n = while_cfg_\<alpha>n c,
  gen_predecessors = while_cfg_predecessors c,
  gen_Entry = while_cfg_Entry c,
  gen_defs = while_cfg_defs c,
  gen_uses = while_cfg_uses c
\<rparr>"

lemma  while_path_graph_pathD: "While_CFG.path c n es m \<Longrightarrow> while.path2 c n (n#map targetnode es) m"
  unfolding while.path2_def
apply (induction n es m rule: While_CFG.path.induct)
 apply clarsimp
 apply (rule while.path.intros)
 apply (auto 4 4 simp: while_cfg_defs valid_node_def While_CFG.valid_node_def)[1]
apply clarsimp
apply (rule while.path.intros)
 apply assumption
apply clarsimp
apply (subst while_cfg_predecessors_def)
apply (rename_tac n ed m)
apply (rule_tac a="sorted_list_of_set {sourcenode e |e. valid_edge c e \<and> targetnode e = m}" in someI2)
 using sorted_list_of_set [of "{sourcenode e |e. valid_edge c e \<and> targetnode e = m}" for m]
 apply (erule_tac x=m in meta_allE)
 apply (erule meta_impE)
  apply (rule finite_subset [OF _ finite_valid_nodes [of "c"]])
  apply (clarsimp simp: valid_node_def)
  apply (rule_tac x=x in exI)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=m in exI)
  apply simp
 apply simp
apply clarsimp
by (rule exI)

lemma Uses_Entry [simp]: "Uses c (_Entry_) = {}"
  unfolding Uses.simps by auto

lemma in_Uses_valid_node: "V \<in> Uses c n \<Longrightarrow> valid_node c n"
  by (auto dest!: label_less_num_inner_nodes less_num_nodes_edge
    simp: Uses.simps valid_node_def valid_edge_def)

interpretation while_SI_CFG_wf:
  SingleInstruction_CFG_wf "while_cfg_\<alpha>n cmd" "while_cfg_predecessors cmd" "while_cfg_Entry cmd" "while_cfg_defs cmd" "while_cfg_uses cmd"
  for cmd
apply unfold_locales
       apply (clarsimp simp: while_cfg_defs)
       using WCFG_intros(1) valid_edge_def valid_node_def apply auto[1]
      apply (clarsimp simp: while_cfg_defs)
      apply (subgoal_tac "{n. \<exists>a. valid_edge (cmd) (n, a, (_Entry_))} = {}")
       apply auto[1]
      apply auto[1]
     apply (subst(asm) while_cfg_\<alpha>n_def)
     apply simp
     apply (drule valid_node_Entry_path)
     apply clarsimp
     apply (drule while_path_graph_pathD)
     apply (auto simp: while_cfg_Entry_def)[1]
    apply (clarsimp simp: while_cfg_defs)
   apply (subgoal_tac "{v. \<exists>n. v \<in> Uses (cmd) n} = (\<Union>n \<in> Collect (valid_node (cmd)). Uses (cmd) n)")
    apply simp
   apply (auto dest: in_Uses_valid_node)[1]
  apply (auto dest!: label_less_num_inner_nodes less_num_nodes_edge
    simp: Uses.simps valid_node_def valid_edge_def while_cfg_defs)[1]
 apply (clarsimp simp: while_cfg_defs)
apply (clarsimp simp: SSA_CFG.CFG_wf_axioms_def CFG_base.defAss'_def)
apply (rule_tac x="(_Entry_)" in bexI)
 apply (auto simp: while_cfg_defs)[1]
apply (cut_tac xs=ns in hd_in_butlast)
 apply (erule while.path2_cases)
  apply (auto simp: while_cfg_Entry_def while_cfg_uses_def dest: while.path2_not_Nil3 "while.path2_hd")
done

lift_definition si_while_cfg_wf :: "cmd \<Rightarrow> (w_node, vname) si_cfg_wf"
  is gen_while_cfg
  unfolding gen_while_cfg_def
  by simp unfold_locales

definition "build_ssa cmd = gen_ssa_wf_notriv_substAll (gen_ssa_cfg_wf (si_wf_disj_cfg_wf (si_while_cfg_wf cmd)))"

end
