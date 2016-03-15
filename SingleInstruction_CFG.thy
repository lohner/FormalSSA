theory SingleInstruction_CFG
imports SSA_CFG Generic_Interpretation
begin

datatype node'_part = PhisUses | Defs
type_synonym 'node node' = "'node \<times> node'_part"

lemma node'_cases:
  obtains (PhisUses) n' where "n = (n',PhisUses)"
|         (Defs)     n' where "n = (n',Defs)"
  by (cases n, case_tac b, auto)

lemma[dest!]: "x \<noteq> PhisUses \<Longrightarrow> x = Defs" by (cases x, simp)
lemma[dest!]: "x \<noteq> Defs \<Longrightarrow> x = PhisUses" by (cases x, auto)

instantiation node'_part :: linorder
begin
  definition[simp]: "less_node'_part n m \<equiv> n = PhisUses \<and> m = Defs"

  definition[simp]: "less_eq_node'_part (n::node'_part) m \<equiv> n = m \<or> n < m"

  instance by intro_classes auto
end

locale SingleInstruction_CFG = CFG_base \<alpha>n predecessors Entry "defs" "uses"
+ graph_Entry \<alpha>n predecessors Entry
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry :: "'node" and
  "defs" :: "'node \<Rightarrow> 'var::linorder set" and
  "uses" :: "'node \<Rightarrow> 'var set" +
assumes defs_finite: "finite (defs n)"
assumes uses_in_\<alpha>n: "v \<in> uses n \<Longrightarrow> n \<in> set \<alpha>n"
assumes uses_finite: "finite (uses n)"
begin
  definition[code]: "disj_\<alpha>n = List.maps (\<lambda>n. [(n, PhisUses), (n, Defs)]) \<alpha>n"
  definition[code]: "disj_predecessors \<equiv> \<lambda>(n,part). case part of
    PhisUses \<Rightarrow> map (\<lambda>n. (n, Defs)) (predecessors n)
  | Defs     \<Rightarrow> if n \<in> set \<alpha>n then [(n, PhisUses)] else []"
  definition[code]: "disj_Entry = (Entry, PhisUses)"
  definition[code]: "disj_defs \<equiv> \<lambda>(n,part). case part of
    PhisUses \<Rightarrow> {}
  | Defs     \<Rightarrow> defs n"
  definition[code]: "disj_uses \<equiv> \<lambda>(n,part). case part of
    PhisUses \<Rightarrow> uses n
  | Defs     \<Rightarrow> {}"

  declare List.maps_def[simp]

  lemma disj_\<alpha>n[simp]: "(n,p) \<in> set disj_\<alpha>n \<longleftrightarrow> n \<in> set \<alpha>n"
    by (cases p, auto simp: disj_\<alpha>n_def)

  lemma distinct_disj_\<alpha>n: "distinct disj_\<alpha>n"
    unfolding disj_\<alpha>n_def List.maps_def
    by (rule distinct_concat, auto simp: \<alpha>n_distinct inj_on_def distinct_map)

  sublocale disj: graph_path_base disj_\<alpha>n disj_predecessors .

  lemma disj_inEdges_pred: "set (disj.inEdges n) = pred (disj.\<alpha> ()) n"
    by (cases n, auto simp: "disj.inEdges_def" pred_def disj.\<alpha>e_def)

  lemma PhisUses_disj_predecessors [simp]: "(n,PhisUses) \<in> set (disj_predecessors m) \<longleftrightarrow> m = (n,Defs) \<and> n \<in> set \<alpha>n"
    by (auto simp: disj_predecessors_def split: node'_part.splits)

  lemma Defs_disj_predecessors [simp]: "(n,Defs) \<in> set (disj_predecessors m) \<longleftrightarrow> (\<exists>m'. m = (m',PhisUses) \<and> n \<in> set (predecessors m'))"
    by (auto simp: disj_predecessors_def split: node'_part.splits)

  lemma disj_predecessor_is_node: "n \<in> set (disj_predecessors m) \<Longrightarrow> n \<in> set disj_\<alpha>n"
    by (auto simp: disj_predecessors_def split: node'_part.splits)

  lemma disj_successor_is_node: "n \<in> set (disj_predecessors m) \<Longrightarrow> m \<in> set disj_\<alpha>n"
    by (auto simp: disj_predecessors_def split: node'_part.splits)

  lemma finite_disj_\<alpha>e: "finite disj.\<alpha>e"
    by (rule finite_subset[of _ "set disj_\<alpha>n \<times> {()} \<times> set disj_\<alpha>n"])
       (auto simp: disj.\<alpha>e_def dest: disj_predecessor_is_node disj_successor_is_node)

  sublocale disj: graph_path disj_\<alpha>n disj_predecessors
  apply unfold_locales
        apply (simp add: disj_\<alpha>n_def)
       apply (simp add: finite_disj_\<alpha>e)
      apply (auto simp: disj.\<alpha>e_def dest: disj_predecessor_is_node)[1]
     apply (auto simp: disj.\<alpha>e_def dest: disj_successor_is_node)[1]
    apply (rule set_iterator_I)
      prefer 3
      apply (simp add: foldri_def)
     apply (simp add: distinct_disj_\<alpha>n)
    apply simp
   unfolding disj_inEdges_pred[symmetric]
   apply (rule set_iterator_foldri_correct)
   unfolding "disj.inEdges_def"
   apply (auto simp: disj_predecessors_def distinct_map distinct_predecessors split: node'_part.split)
  done

  definition "disj_pathElems p ns p' \<equiv>
    let ns = List.maps (\<lambda>n. [(n, PhisUses), (n, Defs)]) ns in
    let ns = if p = Defs then tl ns else ns in
    if p' = PhisUses then butlast ns else ns"

  lemma disj_pathElems_empty [simp]: "disj_pathElems p [] p' = []"
    by (auto simp: disj_pathElems_def Let_def)

  lemma hd_disj_pathElems [simp]: "disj_pathElems p ns p' \<noteq> [] \<Longrightarrow> hd (disj_pathElems p ns p') = (hd ns,p)"
    by (cases ns, auto simp: disj_pathElems_def Let_def)

  lemma disj_pathElems_trivial [simp]: "disj_pathElems p [n] p = [(n,p)]"
    by (auto simp: disj_pathElems_def Let_def)

  lemma disj_pathElems_cons_Defs [simp]: "ns \<noteq> [] \<Longrightarrow> disj_pathElems Defs (n#ns) p' = (n, Defs)#disj_pathElems PhisUses ns p'"
    by (auto simp: disj_pathElems_def Let_def)

  lemma disj_pathElems_cons_PhisUses: "ns \<noteq> [] \<Longrightarrow> disj_pathElems PhisUses ns p' = (hd ns, PhisUses)#disj_pathElems Defs ns p'"
    by (cases ns, auto simp: disj_pathElems_def Let_def)

  lemma butlast_Defs_in_disj_pathElems: "n \<in> set (butlast ns) \<Longrightarrow> (n, Defs) \<in> set (disj_pathElems PhisUses ns p)"
    by (cases ns rule: rev_cases, auto simp: disj_pathElems_def Let_def butlast_append)

  lemma path2_to_disj_path2:
    assumes "path2 n ns m" "p \<le> p'"
    shows "disj.path2 (n,p) (disj_pathElems p ns p') (m,p')"
  using assms(1) proof (induction rule: path2_induct)
    case empty_path
    have[simp]: "m \<in> set \<alpha>n" using assms by auto
    show ?case
    proof (cases "p = p'")
      case True
      thus ?thesis
        by auto
    next
      case False
      with empty_path assms(2) have [simp]: "p = PhisUses" "p' = Defs"
        by auto
      show ?thesis
        by (simp add: disj_pathElems_cons_PhisUses, rule disj.Cons_path2, rule disj.empty_path2, auto)
    qed
  next
    case (Cons_path ns n' n)
    have IH: "disj.path2 (n,p) (disj_pathElems p ns p') (m,p')"
      by (rule Cons_path.IH)
    hence [simp]: "ns \<noteq> []" by (cases ns, auto)
    from IH have [simp]: "hd ns = n" by - (frule disj.path2_hd, subst(asm) hd_disj_pathElems, auto)
    show ?case
    apply (cases p)
     apply simp
     apply (subst disj_pathElems_cons_PhisUses)
      apply simp
     apply simp
     apply (rule disj.Cons_path2)
      apply (rule disj.Cons_path2)
       using IH apply simp
      using Cons_path.hyps(2) apply auto[2]
     apply auto[1]
    apply (subst disj_pathElems_cons_PhisUses)
     apply simp
    apply (rule disj.Cons_path2)
     apply (rule disj.Cons_path2)
      using IH apply simp
     using IH Cons_path.hyps(2) by auto
  qed

  lemma disj_path2_to_path2:
    assumes "disj.path2 n ns m"
    obtains ns' where "path2 (fst n) ns' (fst m)" "disj_pathElems (snd n) ns' (snd m) = ns"
  using assms proof (induction rule: "disj.path2_induct")
    case empty_path
    from assms have "fst m \<in> set \<alpha>n"
      by - (drule disj.path2_tl_in_\<alpha>n, auto simp: disj_\<alpha>n_def)
    thus ?case by - (rule empty_path(1), auto simp: disj_pathElems_trivial)
  next
    case (Cons_path ns n' n)
    show ?case
    proof (rule Cons_path.IH)
      fix ns'
      assume ns': "fst n\<comment>ns'\<rightarrow>fst m" "disj_pathElems (snd n) ns' (snd m) = ns"
      hence[simp]: "ns' \<noteq> []" by auto
      show thesis
      proof (cases n' rule: node'_cases)
        case[simp]: (PhisUses n')
        from Cons_path(2) have[simp]: "n' = fst n" "snd n = Defs"
          by (auto simp: disj_predecessors_def split: node'_part.splits)
        from ns' show ?thesis
          by - (rule Cons_path.prems(1), auto dest: path2_hd simp: disj_pathElems_cons_PhisUses)
      next
        case[simp]: (Defs n')
        from Cons_path(2) have "n' \<in> set (predecessors (fst n))" and[simp]: "snd n = PhisUses"
          by (auto simp: disj_predecessors_def split: node'_part.splits)
        with Cons_path(3) ns' show ?thesis
          by - (rule Cons_path.prems(1), auto simp: disj_pathElems_cons_Defs)
      qed
    qed
  qed

  sublocale disj: CFG disj_\<alpha>n disj_predecessors disj_Entry disj_defs disj_uses
  apply unfold_locales
        apply (simp add: disj_\<alpha>n_def disj_Entry_def)
       apply (simp add: disj_predecessors_def disj_Entry_def)
      apply (subst(asm) disj_\<alpha>n_def disj_Entry_def)
      apply (auto simp: disj_Entry_def dest!: Entry_reaches path2_to_disj_path2[where p=PhisUses])[1]
     apply (auto simp: disj_defs_def disj_uses_def split: node'_part.splits)[1]
    apply (auto simp: disj_defs_def split: node'_part.split intro: defs_finite)[1]
   apply (auto simp: disj_uses_def disj_\<alpha>n_def split: node'_part.splits intro: uses_in_\<alpha>n)[1]
  apply (auto simp: disj_uses_def split: node'_part.splits intro: uses_finite)
  done
end

locale SingleInstruction_CFG_wf = SingleInstruction_CFG \<alpha>n predecessors Entry "defs" "uses"
for
  \<alpha>n :: "'node::linorder list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry :: "'node" and
  "defs" :: "'node \<Rightarrow> 'var::linorder set" and
  "uses" :: "'node \<Rightarrow> 'var set" +
(* note that, in contrast to @{term defAss'}, the last node must be excluded *)
assumes def_ass_uses: "\<forall>m \<in> set \<alpha>n. \<forall>v \<in> uses m. \<forall>ns. Entry\<comment>ns\<rightarrow>m \<longrightarrow> (\<exists>n \<in> set (butlast ns). v \<in> defs n)"
begin
  lemma disj_defAss':
    assumes "m \<in> set disj_\<alpha>n" "v \<in> disj_uses m"
    shows "disj.defAss' m v"
  proof (rule "disj.defAss'I")
    fix ns
    assume "disj.path2 disj_Entry ns m"
    then obtain ns' where ns': "Entry\<comment>ns'\<rightarrow>fst m" "disj_pathElems PhisUses ns' (snd m) = ns"
      by (rule disj_path2_to_path2, simp add: disj_Entry_def)
    with assms(2) obtain n where "n \<in> set (butlast ns')" "v \<in> defs n"
      using def_ass_uses[rule_format, of "fst m" v ns'] by (auto simp: disj_uses_def dest!: path2_tl_in_\<alpha>n split:node'_part.splits)
    with ns'(2) show "\<exists>n\<in>set ns. v \<in> disj_defs n"
      by - (rule bexI[where x="(n,Defs)"], auto simp: disj_defs_def butlast_Defs_in_disj_pathElems)
  qed

  sublocale disj: CFG_Construct_linorder disj_\<alpha>n disj_predecessors disj_Entry disj_defs disj_uses
    by unfold_locales (auto intro!: disj_defAss')

  lift_definition disj_cfg_wf :: "('node node', 'var) gen_cfg_wf" is "\<lparr>
      gen_\<alpha>n = disj_\<alpha>n,
      gen_predecessors = disj_predecessors,
      gen_Entry = disj_Entry,
      gen_defs = disj_defs,
      gen_uses = disj_uses
    \<rparr>"
    by simp unfold_locales

  lemma [code]: "disj_predecessors =
    (let cache = Mapping.tabulate disj_\<alpha>n (\<lambda>(n,part). case part of
        PhisUses \<Rightarrow> map (\<lambda>n. (n, Defs)) (predecessors n)
      | Defs     \<Rightarrow> [(n, PhisUses)]) in
    (\<lambda>n. case_option [] id (Mapping.lookup cache n)))"
    unfolding disj_predecessors_def
    by transfer (auto simp: map_of_map_if_conv empty_preds_of_nonnode split: option.splits node'_part.splits)

  (*
  definition "ssa_defs n = disj.defs' (n,Defs)"
  definition "ssa_uses n = disj.uses' (n,PhisUses)"
  definition "ssa_phis = Mapping.map (\<lambda>(n,v). ((n,PhisUses),v)) id disj.phis'_code"

  sublocale ssa: CFG_SSA_Transformed \<alpha>n predecessors Entry defs "uses" ssa_defs ssa_uses "Mapping.lookup ssa_phis" disj.var
  apply unfold_locales
  *)

  definition "disj_ssa_cfg \<equiv> let (uses,phis) = disj.uses'_phis' in \<lparr>
    gen_\<alpha>n = disj_\<alpha>n,
    gen_predecessors = disj_predecessors,
    gen_Entry = disj_Entry,
    gen_defs = disj_defs,
    gen_uses = disj_uses,
    gen_ssa_defs = disj.defs',
    gen_ssa_uses = uses,
    gen_phis = phis,
    gen_var = gen_wf_var
  \<rparr>"
end

typedef ('node, 'var) si_cfg_wf = "{g :: ('node::linorder, 'var::linorder) gen_cfg.
  SingleInstruction_CFG_wf (gen_\<alpha>n g) (gen_predecessors g) (gen_Entry g) (gen_defs g) (gen_uses g)}"
apply (rule exI[where x="trivial_gen_cfg undefined"])
apply auto
apply unfold_locales
by (auto simp: gen_cfg.defs graph_path_base.path2_def pred_def "graph_path_base.\<alpha>e_def" "graph_path_base_base.inEdges_def" List.maps_def intro!: graph_path_base.path.intros(1) exI)


setup_lifting type_definition_si_cfg_wf

lift_definition si_wf_\<alpha>n :: "('node::linorder, 'var::linorder) si_cfg_wf \<Rightarrow> 'node list" is gen_\<alpha>n .
lift_definition si_wf_predecessors :: "('node::linorder, 'var::linorder) si_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'node list" is gen_predecessors .
lift_definition si_wf_Entry :: "('node::linorder, 'var::linorder) si_cfg_wf \<Rightarrow> 'node" is gen_Entry .
lift_definition si_wf_defs :: "('node::linorder, 'var::linorder) si_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'var set" is gen_defs .
lift_definition si_wf_uses :: "('node::linorder, 'var::linorder) si_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'var set" is gen_uses .

global_interpretation si_wf: SingleInstruction_CFG_wf "si_wf_\<alpha>n g" "si_wf_predecessors g" "si_wf_Entry g" "si_wf_defs g" "si_wf_uses g"
for g
defines
  si_wf_disj_\<alpha>n = "si_wf.disj_\<alpha>n" and
  si_wf_disj_predecessors = "si_wf.disj_predecessors" and
  si_wf_disj_Entry = "si_wf.disj_Entry" and
  si_wf_disj_defs = "si_wf.disj_defs" and
  si_wf_disj_uses = "si_wf.disj_uses" and
  si_wf_disj_cfg_wf = "si_wf.disj_cfg_wf"
  by transfer

end
