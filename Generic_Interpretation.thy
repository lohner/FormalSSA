(*  Title:      Generic_Interpretation.thy
    Author:     Sebastian Ullrich, Denis Lohner
*)

subsection {* Generic Code Extraction Based on typedefs *}

theory Generic_Interpretation
imports
Construct_SSA_code
Construct_SSA_notriv_code
RBT_Mapping_Exts
"~~/src/HOL/Library/RBT_Set"
"~~/src/HOL/Library/Code_Target_Numeral"
begin

record ('node, 'var) gen_cfg =
  gen_\<alpha>n :: "'node list"
  gen_predecessors :: "'node \<Rightarrow> 'node list"
  gen_Entry :: "'node"
  gen_defs :: "'node \<Rightarrow> 'var set"
  gen_uses :: "'node \<Rightarrow> 'var set"

abbreviation "trivial_gen_cfg ext \<equiv> gen_cfg_ext [undefined] (const []) undefined (const {}) (const {}) ext"

lemma set_iterator_foldri_Nil [simp, intro!]: "set_iterator (foldri []) {}"
  by (rule set_iterator_I; simp add: foldri_def)

lemma set_iterator_foldri_one [simp, intro!]: "set_iterator (foldri [a]) {a}"
  by (rule set_iterator_I; simp add: foldri_def)

typedef ('node, 'var) gen_cfg_wf = "{g :: ('node::linorder, 'var::linorder) gen_cfg.
  CFG_wf (gen_\<alpha>n g) (gen_predecessors g) (gen_Entry g) (gen_defs g) (gen_uses g)}"
apply (rule exI[where x="trivial_gen_cfg undefined"])
apply auto
apply unfold_locales
by (auto simp: gen_cfg.defs graph_path_base.path2_def pred_def "graph_path_base.\<alpha>e_def" "graph_path_base_base.inEdges_def" List.maps_def intro!: graph_path_base.path.intros(1) exI)

setup_lifting type_definition_gen_cfg_wf

lift_definition gen_wf_\<alpha>n :: "('node::linorder, 'var::linorder) gen_cfg_wf \<Rightarrow> 'node list" is gen_\<alpha>n .
lift_definition gen_wf_predecessors :: "('node::linorder, 'var::linorder) gen_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'node list" is gen_predecessors .
lift_definition gen_wf_Entry :: "('node::linorder, 'var::linorder) gen_cfg_wf \<Rightarrow> 'node" is gen_Entry .
lift_definition gen_wf_defs :: "('node::linorder, 'var::linorder) gen_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'var set" is gen_defs .
lift_definition gen_wf_uses :: "('node::linorder, 'var::linorder) gen_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'var set" is gen_uses .

global_interpretation gen_wf: CFG_Construct_linorder "gen_wf_\<alpha>n g" "gen_wf_predecessors g" "gen_wf_Entry g" "gen_wf_defs g" "gen_wf_uses g"
for g
defines
  gen_wf_successors = gen_wf.successors and
  gen_wf_defs' = gen_wf.defs' and
  gen_wf_vars = gen_wf.vars and
  gen_wf_var = gen_wf.var and
  gen_wf_readVariableRecursive = gen_wf.readVariableRecursive and
  gen_wf_readArgs = gen_wf.readArgs and
  gen_wf_uses'_phis' = gen_wf.uses'_phis'
  unfolding CFG_Construct_linorder_def CFG_Construct_wf_def CFG_Construct_def
  by transfer (simp add: CFG_wf_def)

record ('node, 'var, 'val) gen_ssa_cfg = "('node, 'var) gen_cfg" +
  gen_ssa_defs :: "'node \<Rightarrow> 'val set"
  gen_ssa_uses :: "('node, 'val set) mapping"
  gen_phis :: "('node, 'val) phis_code"
  gen_var :: "'val \<Rightarrow> 'var"

typedef ('node, 'var, 'val) gen_ssa_cfg_wf = "{g :: ('node::linorder, 'var::linorder, 'val::linorder) gen_ssa_cfg.
  CFG_SSA_Transformed_code  (gen_\<alpha>n g) (gen_predecessors g) (gen_Entry g) (gen_defs g) (gen_uses g) (gen_ssa_defs g) (gen_ssa_uses g) (gen_phis g) (gen_var g)}"
apply (rule exI[where x ="trivial_gen_cfg \<lparr> gen_ssa_defs = const {}, gen_ssa_uses = Mapping.empty, gen_phis = Mapping.empty, gen_var = undefined, \<dots> = undefined \<rparr>"])
apply auto
apply unfold_locales
by (auto simp: gen_cfg.defs graph_path_base.path2_def graph_path_base.\<alpha>e_def "graph_path_base_base.inEdges_def" List.maps_def dom_def Mapping.lookup_empty CFG_SSA_base.CFG_SSA_defs pred_def intro!: graph_path_base.path.intros(1) exI)

setup_lifting type_definition_gen_ssa_cfg_wf

lift_definition gen_ssa_wf_\<alpha>n :: "('node::linorder, 'var::linorder, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node list" is gen_\<alpha>n .
lift_definition gen_ssa_wf_predecessors :: "('node::linorder, 'var::linorder, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'node list" is gen_predecessors .
lift_definition gen_ssa_wf_Entry :: "('node::linorder, 'var::linorder, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node" is gen_Entry .
lift_definition gen_ssa_wf_defs :: "('node::linorder, 'var::linorder, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'var set" is gen_defs .
lift_definition gen_ssa_wf_uses :: "('node::linorder, 'var::linorder, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'var set" is gen_uses .
lift_definition gen_ssa_wf_ssa_defs :: "('node::linorder, 'var::linorder, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'val set" is gen_ssa_defs .
lift_definition gen_ssa_wf_ssa_uses :: "('node::linorder, 'var::linorder, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> ('node, 'val set) mapping" is gen_ssa_uses .
lift_definition gen_ssa_wf_phis :: "('node::linorder, 'var::linorder, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> ('node, 'val) phis_code" is gen_phis .
lift_definition gen_ssa_wf_var :: "('node::linorder, 'var::linorder, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'val \<Rightarrow> 'var" is gen_var .

global_interpretation uninst: CFG_SSA_wf_base_code "gen_ssa_wf_\<alpha>n g" "gen_ssa_wf_predecessors g" "gen_ssa_wf_Entry g" "gen_ssa_wf_ssa_defs g" u p
  for g u p
  defines
      uninst_successors = uninst.successors
  and uninst_phiDefs = uninst.phiDefs
  and uninst_phiUses = uninst.phiUses
  and uninst_allDefs = uninst.allDefs
  and uninst_allUses = uninst.allUses
  and uninst_allVars = uninst.allVars
  and uninst_isTrivialPhi = uninst.isTrivialPhi
  and uninst_trivial = uninst.trivial_code
  and uninst_redundant = uninst.redundant_code
  and uninst_phi = uninst.phi
  and uninst_defNode = uninst.defNode
  and uninst_trivial_phis = uninst.trivial_phis
  and uninst_phidefNodes = uninst.phidefNodes
  and uninst_useNodes_of = uninst.useNodes_of
  and uninst_phiNodes_of = uninst.phiNodes_of
.

definition "uninst_chooseNext u p \<equiv> Max (uninst_trivial_phis (p))"

global_interpretation gen_ssa_wf_notriv: CFG_SSA_Transformed_code "gen_ssa_wf_\<alpha>n g" "gen_ssa_wf_predecessors g" "gen_ssa_wf_Entry g" "gen_ssa_wf_defs g" "gen_ssa_wf_uses g" "gen_ssa_wf_ssa_defs g" "gen_ssa_wf_ssa_uses g" "gen_ssa_wf_phis g" "gen_ssa_wf_var g"
for g
  by transfer

global_interpretation gen_ssa_wf_notriv: CFG_SSA_Transformed_notriv_linorder_code "gen_ssa_wf_\<alpha>n g" "gen_ssa_wf_predecessors g" "gen_ssa_wf_Entry g" "gen_ssa_wf_defs g" "gen_ssa_wf_uses g" "gen_ssa_wf_ssa_defs g" "gen_ssa_wf_ssa_uses g" "gen_ssa_wf_phis g" "gen_ssa_wf_var g" uninst_chooseNext
for g
defines
  gen_ssa_wf_notriv_substAll = gen_ssa_wf_notriv.substAll and
  gen_ssa_wf_notriv_substAll_efficient = gen_ssa_wf_notriv.substAll_efficient
proof
  fix u p
  assume "CFG_SSA_Transformed (gen_ssa_wf_\<alpha>n g) (gen_ssa_wf_predecessors g) (gen_ssa_wf_Entry g) (gen_ssa_wf_defs g) (gen_ssa_wf_uses g) (gen_ssa_wf_ssa_defs g) u p (gen_ssa_wf_var g)"
  then interpret i: CFG_SSA_Transformed "gen_ssa_wf_\<alpha>n g" "gen_ssa_wf_predecessors g" "gen_ssa_wf_Entry g" "gen_ssa_wf_defs g" "gen_ssa_wf_uses g" "gen_ssa_wf_ssa_defs g" u p "gen_ssa_wf_var g" .
  obtain u' where [simp]: "usesOf u' = u"
    apply (erule_tac x="Mapping.Mapping (\<lambda>n. if u n = {} then None else Some (u n))" in meta_allE)
    by (erule meta_impE) (auto 4 4 simp: o_def usesOf_def [abs_def] split: option.splits if_splits)
  interpret code: CFG_SSA_wf_code "gen_ssa_wf_\<alpha>n g" "gen_ssa_wf_predecessors g" "gen_ssa_wf_Entry g" "gen_ssa_wf_ssa_defs g" u' "Mapping.Mapping (p)"
  unfolding CFG_SSA_wf_code_def CFG_SSA_code_def
  apply simp_all
  apply (rule conjI)
  by unfold_locales

  assume red: "i.redundant"
  let ?cN = "uninst_chooseNext (u) (Mapping.Mapping (p))"

  show "?cN \<in> dom (p) \<and> i.trivial (snd ?cN)"
  unfolding uninst_chooseNext_def
  unfolding uninst_trivial_phis_def code.trivial_phis
  apply (rule CollectD[where a="Max _"])
  apply (rule subsetD[OF _ Max_in])
    apply auto[1]
   apply (rule finite_subset[OF _ i.phis_finite])
   using red
   apply (auto simp: i.redundant_def[abs_def])
  apply (frule code.trivial_phi[simplified])
  apply (auto simp: i.phi_def)
  done
qed (auto simp: uninst_chooseNext_def uninst_trivial_phis_def CFG_SSA_wf_base_code.trivial_phis_def)

global_interpretation uninst_code: CFG_SSA_Transformed_notriv_base_code "gen_ssa_wf_\<alpha>n g" "gen_ssa_wf_predecessors g" "gen_ssa_wf_Entry g" "gen_ssa_wf_defs g" "gen_ssa_wf_uses g" "gen_ssa_wf_ssa_defs g" u p "gen_ssa_wf_var g" uninst_chooseNext
for g and u and p
defines
  uninst_code_step_code = uninst_code.step_codem and
  uninst_code_phis' = uninst_code.phis'_codem and
  uninst_code_uses' = uninst_code.uses'_codem and
  uninst_code_substNext = uninst_code.substNext_code and
  uninst_code_substitution = uninst_code.substitution_code and
  uninst_code_triv_phis' = uninst_code.triv_phis' and
  uninst_code_nodes_of_uses' = uninst_code.nodes_of_uses' and
  uninst_code_nodes_of_phis' = uninst_code.nodes_of_phis'
.

lift_definition gen_cfg_wf_extend :: "('a::linorder, 'b::linorder) gen_cfg_wf \<Rightarrow> 'c \<Rightarrow> ('a, 'b, 'c) gen_cfg_scheme"
  is gen_cfg.extend .

lemma gen_\<alpha>n_wf_extend [simp]:
  "gen_\<alpha>n (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_\<alpha>n gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_\<alpha>n_def)

lemma gen_predecessors_wf_extend [simp]:
  "gen_predecessors (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_predecessors gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_predecessors_def)

lemma gen_Entry_wf_extend [simp]:
  "gen_Entry (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_Entry gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_Entry_def)

lemma gen_defs_wf_extend [simp]:
  "gen_defs (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_defs gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_defs_def)

lemma gen_uses_wf_extend [simp]:
  "gen_uses (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_uses gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_uses_def)

lemma gen_ssa_defs_wf_extend [simp]:
  "gen_ssa_defs (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = d"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs)

lemma gen_ssa_uses_wf_extend [simp]:
  "gen_ssa_uses (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = u"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs)

lemma gen_phis_wf_extend [simp]:
  "gen_phis (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = p"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs)

lemma gen_var_wf_extend [simp]:
  "gen_var (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = v"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs)

lemma CFG_SSA_Transformed_codeI:
  assumes "CFG_SSA_Transformed \<alpha>n predecessors Entry oldDefs oldUses defs (lookup_multimap uses) (Mapping.lookup phis) var"
  and "\<And>g. Mapping.keys uses \<subseteq> set \<alpha>n"
  shows "CFG_SSA_Transformed_code \<alpha>n predecessors Entry oldDefs oldUses defs uses phis var"
proof -
  interpret CFG_SSA_Transformed \<alpha>n predecessors Entry oldDefs oldUses "defs" "lookup_multimap uses" "Mapping.lookup phis" var
    by fact
  have [simp]: "usesOf = lookup_multimap"
    by (intro ext) (clarsimp simp: lookup_multimap_def)
  from assms
  show ?thesis
  apply unfold_locales
                   apply (auto intro!: defs_uses_disjoint)[1]
                  apply (rule defs_finite)
                 apply (rule uses_in_\<alpha>n)
                 apply simp
                apply (clarsimp split: option.splits)
              apply (rule phis_finite)
             apply (rule phis_in_\<alpha>n; simp)
            apply (rule phis_wf; simp)
           apply (rule simpleDefs_phiDefs_disjoint; simp)
          apply (rule allDefs_disjoint; simp)
         apply (rule allUses_def_ass; simp add: comp_def)
        apply (rule Entry_no_phis)
       apply (rule oldDefs_def)
      apply (auto intro!: oldUses_def)[1]
     apply (rule conventional; simp add: comp_def)
    apply (rule phis_same_var; simp)
   apply (rule allDefs_var_disjoint; simp)
  by auto
qed

lift_definition gen_ssa_cfg_wf :: "('node::linorder, 'var::linorder) gen_cfg_wf \<Rightarrow> ('node, 'var , ('node,'var) ssaVal) gen_ssa_cfg_wf"
  is "\<lambda>g. let (uses,phis) = gen_wf_uses'_phis' g in (gen_cfg_wf_extend g)\<lparr>
    gen_ssa_defs = gen_wf_defs' g,
    gen_ssa_uses = uses,
    gen_phis = phis,
    gen_var = gen_wf_var
  \<rparr>"
apply (simp add: Let_def gen_wf_uses'_phis'_def split_beta)
apply (subst CFG_Construct_linorder.snd_uses'_phis'[symmetric])
 apply unfold_locales[1]
apply (rule CFG_SSA_Transformed_codeI)
 apply (subst CFG_Construct_linorder.fst_uses'_phis'[symmetric])
  apply unfold_locales[1]
 apply (subst_tac CFG_Construct_linorder.phis'_code_def)
  apply unfold_locales[1]
 apply simp
 apply unfold_locales[1]
apply (rule CFG_Construct_linorder.fst_uses'_phis'_in_\<alpha>n)
by unfold_locales

declare uninst.defNode_code[abs_def, code] uninst.allVars_code[abs_def, code] uninst.allUses_def[abs_def, code] uninst.allDefs_def[abs_def, code]
  uninst.phiUses_code[abs_def, code] uninst.phi_def[abs_def, code] uninst.redundant_code_def[abs_def, code]
declare uninst_code.uses'_code_def[abs_def, code] uninst_code.substNext_code_def[abs_def, code] uninst_code.substitution_code_def[abs_def, folded uninst_phi_def, code]
declare uninst_code.phis'_code_def[folded uninst_code_substNext_def, code] uninst_code.step_code_def[folded uninst_code.uses'_code_def uninst_code.phis'_code_def, code]
  uninst_code.cond_code_def[folded uninst_redundant_def, code]
declare gen_ssa_wf_notriv.substAll_efficient_def
  [folded uninst_code_nodes_of_phis'_def uninst_code_nodes_of_uses'_def uninst_code_triv_phis'_def
    uninst_code_substitution_def
    uninst_code_step_code_def uninst_code_phis'_def uninst_code_uses'_def uninst_trivial_phis_def
    uninst_phidefNodes_def uninst_useNodes_of_def uninst_phiNodes_of_def, code]

declare keys_dom_lookup [symmetric, code_unfold]

definition "map_keys_from_sparse \<equiv> map_keys gen_wf.from_sparse"

declare map_keys_code[OF gen_wf.from_sparse_inj, folded map_keys_from_sparse_def, code]
declare map_keys_from_sparse_def[symmetric, code_unfold]

lemma fold_Cons_commute: "(\<And>a b. \<lbrakk>a \<in> set (x # xs); b \<in> set (x # xs)\<rbrakk> \<Longrightarrow> f a \<circ> f b = f b \<circ> f a)
  \<Longrightarrow> fold f (x # xs) = f x \<circ> (fold f xs)"
  by (simp add: fold_commute)

lemma Union_of_code [code]: "Union_of f (RBT_Set.Set r) = RBT.fold (\<lambda>a _. op \<union> (f a)) r {}"
proof -
  { fix xs
    have "(\<Union>x\<in>{x. (x, ()) \<in> set xs}. f x) = fold (\<lambda>(a,_). op \<union> (f a)) xs {}"
      apply (induction xs)
       apply simp
      by (subst fold_Cons_commute) auto
  }
  note Union_fold = this
  show ?thesis
    unfolding Union_of_def
    by (clarsimp simp: RBT_Set.Set_def RBT.fold_fold RBT.lookup_in_tree) (rule Union_fold [simplified])
qed

definition[code]: "disjoint xs ys = (xs \<inter> ys = {})"

definition "gen_ssa_wf_notriv_substAll' = fst \<circ> gen_ssa_wf_notriv_substAll_efficient"

definition "fold_set f A \<equiv> fold f (sorted_list_of_set A)"
declare fold_set_def [symmetric, code_unfold]
declare fold_set_def
  [where A="RBT_Set.Set r" for r,
    unfolded sorted_list_set fold_keys_def_alt [symmetric,abs_def] fold_keys_def [abs_def],
    code]

end
