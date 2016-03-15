(*  Title:      SSA_Semantics.thy
    Author:     Sebastian Ullrich
*)

section {* Proof of Semantic Equivalence *}

theory SSA_Semantics
imports SSA_CFG
begin

type_synonym ('node, 'var) state = "'var \<rightharpoonup> 'node"

context CFG_SSA_Transformed
begin
  definition step ::
    "'node \<Rightarrow> ('node, 'var) state \<Rightarrow> ('node, 'var) state"
  where
    "step m s v \<equiv> if v \<in> oldDefs m then Some m else s v"

  no_notation Refine_Basic.conc_fun ("\<Down>")

  inductive bs :: "'node list \<Rightarrow> ('node, 'var) state \<Rightarrow> bool" (infix "\<Down>" 50)
  where
    "Entry\<comment>ns\<rightarrow>last ns \<Longrightarrow> ns\<Down>(fold (step) ns Map.empty)"


  definition ssaStep ::
    "'node \<Rightarrow> nat \<Rightarrow> ('node, 'val) state \<Rightarrow> ('node, 'val) state"
  where
    "ssaStep m i s v \<equiv>
      if v \<in> defs m then
        Some m
      else
        case phis (m,v) of
          Some phiParams \<Rightarrow> s (phiParams ! i)
        | None \<Rightarrow> s v"

  inductive ssaBS :: "'node list \<Rightarrow> ('node, 'val) state \<Rightarrow> bool" (infix "\<Down>\<^sub>s" 50)
  where
    empty: "[Entry]\<Down>\<^sub>s(ssaStep (Entry) 0 Map.empty)"
  | snoc: "\<lbrakk>ns\<Down>\<^sub>ss; last ns = predecessors m ! i; m \<in> set \<alpha>n; i < length (predecessors m)\<rbrakk> \<Longrightarrow>
            (ns@[m])\<Down>\<^sub>s(ssaStep m i s)"

  lemma ssaBS_I:
    assumes "Entry\<comment>ns\<rightarrow>n"
    obtains s where "ns\<Down>\<^sub>ss"
  using assms
  proof (atomize_elim, induction rule:path2_rev_induct)
    case (snoc ns m' m)
    then obtain s where s: "ns\<Down>\<^sub>ss" by auto
    from snoc.hyps(2) obtain i where "m' = predecessors m ! i" "i < length (predecessors m)" by (auto simp:in_set_conv_nth)
    with snoc.hyps snoc.prems s show ?case by -(rule exI, erule ssaBS.snoc, auto dest:path2_last)
  qed (auto intro: ssaBS.empty)

  lemma ssaBS_nonempty[simp]: "\<not> ([]\<Down>\<^sub>ss)"
  by (rule notI, cases rule: ssaBS.cases, auto)

  lemma ssaBS_hd[simp]: "ns\<Down>\<^sub>ss \<Longrightarrow> hd ns = Entry"
    apply (induction rule: ssaBS.induct)
     apply (auto simp: hd_append)[1]
    by (case_tac ns; simp)

  lemma equiv_aux:
    assumes "ns\<Down>s" "ns\<Down>\<^sub>ss'" "last ns\<comment>ms\<rightarrow>m" "v \<in> allUses m" "\<forall>n \<in> set (tl ms). var v \<notin> var ` allDefs n"
    shows "s (var v) = s' v"
  using assms(2) assms(1,3-) proof (induction arbitrary: v s ms m)
    case empty
    have "v \<in> defs (Entry)"
    proof-
      from empty.prems(2,3) have "defAss m v" by - (rule allUses_def_ass, auto)
      with empty.prems(2) obtain n where n: "n \<in> set ms" "v \<in> allDefs n" by - (drule defAssD, auto)
      with empty.prems(4) have "n \<notin> set (tl ms)" by auto
      with empty.prems(2) n have "n = Entry" by (cases ms, auto dest: path2_hd)
      with n(2) show ?thesis by (auto simp: allDefs_def)
    qed
    with empty.prems(1) show ?case
      by - (erule bs.cases, auto simp: step_def ssaStep_def oldDefs_def split: option.split)
  next
    case (snoc ns s' n i)
    from snoc.prems(2) have[simp]: "n \<in> set \<alpha>n" "m \<in> set \<alpha>n" by auto
    from snoc.prems(2,3) have[simp]: "v \<in> allVars" by - (rule allUses_in_allVars, auto)
    from snoc.hyps(4) have[simp]: "n \<noteq> Entry" using Entry_unreachable len_greater_imp_nonempty by blast

    show ?case
    proof (cases "var v \<in> var ` allDefs n")
      case True

      have[simp]: "defNode v = n" (is "?n\<^sub>v = _")
      proof-
        from True obtain v' where v': "v' \<in> allDefs n" "var v' = var v" by auto
        from snoc.prems(3) have "defAss m v" by - (rule allUses_def_ass, auto)
        moreover from snoc.prems(1) obtain ns' where ns': "Entry\<comment>ns'\<rightarrow>n" "set ns' \<subseteq> set (ns@[n])" "distinct ns'"
          by (auto elim!: bs.cases intro: simple_path2)
        ultimately have "?n\<^sub>v \<in> set (ns'@tl ms)"
          using snoc.prems(2) by - (drule defAss_defNode, auto elim!: bs.cases dest: path2_app)
        moreover {
          let ?n'' = "last (butlast ns')"
          assume asm: "?n\<^sub>v \<in> set (butlast ns')"
          with ns'(1,3) have[simp]: "?n\<^sub>v \<noteq> n" by (cases ns' rule: rev_cases, auto dest!: path2_last)
          from ns'(1) have "length ns' \<ge> 2" using \<open>n \<noteq> Entry\<close> path2_nontrivial by blast
          with ns' have bns': "Entry\<comment>butlast ns'\<rightarrow>?n''" "?n'' \<in> set (predecessors n)"
            by (auto elim: path2_unsnoc)
          with asm obtain ns'' where ns'': "?n\<^sub>v\<comment>ns''\<rightarrow>?n''" "suffixeq ns'' (butlast ns')" "?n\<^sub>v \<notin> set (tl ns'')"
            by - (rule path2_split_first_last, auto)
          with bns' snoc.prems(2) have "?n\<^sub>v\<comment>(ns''@[n])@tl ms\<rightarrow>m" by - (rule path2_app, auto)
          hence "defNode v' \<notin> set (tl (ns''@[n]@tl ms))"
            using v' snoc.prems(3,4) bns'(2) ns''(1,3)
            by - (rule conventional''[of v _ m], auto intro!: path2_app simp: path2_not_Nil)
          with ns' ns''(1) v'(1) have False by (auto simp: path2_not_Nil)
        }
        ultimately show ?thesis using snoc.prems(4) ns'(1) by (cases ns' rule: rev_cases, auto dest: path2_last)
      qed
      from `v \<in> allVars` show ?thesis
      proof (cases rule: defNode_cases)
        case simpleDef
        thus ?thesis using snoc.prems(1) by - (erule bs.cases, auto simp: step_def ssaStep_def oldDefs_def)
      next
        case phi
        {
          fix v'
          assume asm: "v' \<in> defs n" "var v = var v'"
          with phi have "v' = v" using allDefs_var_disjoint[of n v' v]
            \<open>defNode v = n\<close> \<open>v \<in> allVars\<close> defNode(2) defs_in_allDefs snoc.hyps(3) by blast
          with asm(1) phi have False using simpleDefs_phiDefs_disjoint[of n]
            by (auto dest!: phi_phiDefs)
        }
        note 1 = this
        {
          fix vs
          assume asm: "Entry\<comment>ns @ [n]\<rightarrow>n" "phis (n, v) = Some vs" "var v \<notin> var ` defs n"
          let ?n' = "last ns"
          from asm(1) have "length ns \<ge> 1"
            by (metis One_nat_def \<open>n \<noteq> Entry\<close> append_Nil graph_path_base.path2_def le_0_eq length_0_conv list.sel(1) not_less_eq_eq)
          hence "Entry\<comment>ns\<rightarrow>?n'"
            by - (rule path2_unsnoc[OF asm(1)], auto)
          moreover have "vs ! i \<in> phiUses ?n'" using snoc.hyps(2,4) phis_wf[OF asm(2)]
            by - (rule phiUsesI[OF _ asm(2)], auto simp: set_zip)
          ultimately have "fold (step) ns Map.empty (var (vs ! i)) = s' (vs ! i)"
          by - (rule snoc.IH[where ms4="[?n']" and m4="?n'"], auto intro!: bs.intros)
          hence "fold (step) ns Map.empty (var v) = s' (vs ! i)" using phis_same_var[OF asm(2), of "vs ! i"] snoc.hyps(4) phis_wf[OF asm(2)]
            by auto
        }
        thus ?thesis using phi snoc.prems(1)
          by - (erule bs.cases, auto dest!: 1 simp: step_def ssaStep_def oldDefs_def phi_def)
      qed
    next
      case False
      hence "phis (n, v) = None" by (auto simp: allDefs_def phiDefs_def)
      moreover have "fold (step) ns Map.empty (var v) = s' v"
      proof-
        from snoc.hyps(1) have "length ns \<ge> 1" by (cases ns, auto)
        moreover from snoc.prems(2,4) False have "\<forall>n \<in> set ms. var v \<notin> var ` allDefs n"
          by (cases ms, auto simp: phiDefs_def dest: path2_hd)
        ultimately show ?thesis
          using snoc.prems(1,2,3) by - (rule snoc.IH[where ms4="last ns#ms"], auto elim!: bs.cases intro!: bs.intros elim: path2_unsnoc intro!: Cons_path2)
      qed
      ultimately show ?thesis
        using snoc.prems(1) False by - (erule bs.cases, auto simp: step_def ssaStep_def oldDefs_def defs_in_allDefs)
    qed
  qed

  theorem equiv:
    assumes "ns\<Down>s" "ns\<Down>\<^sub>ss'" "v \<in> uses (last ns)"
    shows "s (var v) = s' v"
  using assms by - (rule equiv_aux[where ms="[last ns]"], auto elim!: bs.cases)
end

end
