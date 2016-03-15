(*  Title:      Minimality.thy
    Author:     Sebastian Ullrich
*)

section {* Minimality *}

text {* We show that every reducible CFG without trivial \pf s is minimal, recreating the proof in~\cite{braun13cc}.
  The original proof is inlined as prose text. *}

theory Minimality
imports SSA_CFG Serial_Rel
begin

context graph_path
begin
  text {* Cytron's definition of path convergence *}
  definition "pathsConverge x xs y ys z \<equiv> x\<comment>xs\<rightarrow>z \<and> y\<comment>ys\<rightarrow>z \<and> length xs > 1 \<and> length ys > 1 \<and> x \<noteq> y \<and>
    (\<forall>j \<in> {0..< length xs}. \<forall>k \<in> {0..<length ys}. xs ! j = ys ! k \<longrightarrow> j = length xs - 1 \<or> k = length ys - 1)"

  text {* Simplified definition *}
  definition "pathsConverge' x xs y ys z \<equiv> x\<comment>xs\<rightarrow>z \<and> y\<comment>ys\<rightarrow>z \<and> length xs > 1 \<and> length ys > 1 \<and> x \<noteq> y \<and>
    set (butlast xs) \<inter> set (butlast ys) = {}"

  lemma pathsConverge'[simp]: "pathsConverge x xs y ys z \<longleftrightarrow> pathsConverge' x xs y ys z"
  proof-
    have "(\<forall>j \<in> {0..< length xs}. \<forall>k \<in> {0..<length ys}. xs ! j = ys ! k \<longrightarrow> j = length xs - 1 \<or> k = length ys - 1)
          \<longleftrightarrow> (\<forall>x' \<in> set (butlast xs). \<forall>y' \<in> set (butlast ys). x' \<noteq> y')"
    proof
      assume 1: "\<forall>j\<in>{0..<length xs}. \<forall>k\<in>{0..<length ys}. xs ! j = ys ! k \<longrightarrow> j = length xs - 1 \<or> k = length ys - 1"
      show "\<forall>x'\<in>set (butlast xs). \<forall>y'\<in>set (butlast ys). x' \<noteq> y'"
      proof (rule, rule, rule)
        fix x' y'
        assume 2: "x' \<in> set (butlast xs)" "y' \<in> set (butlast ys)" and[simp]: "x' = y'"
        from 2(1) obtain j where "xs ! j = x'" "j < length xs - 1" by (rule butlast_idx)
        moreover from this have "j < length xs" by simp
        moreover from 2(2) obtain k where "ys ! k = y'" "k < length ys - 1" by (rule butlast_idx)
        moreover from this have "k < length ys" by simp
        ultimately show False using 1[THEN bspec[where x=j], THEN bspec[where x=k]] by auto
      qed
    next
      assume 1: "\<forall>x'\<in>set (butlast xs). \<forall>y'\<in>set (butlast ys). x' \<noteq> y'"
      show "\<forall>j\<in>{0..<length xs}. \<forall>k\<in>{0..<length ys}. xs ! j = ys ! k \<longrightarrow> j = length xs - 1 \<or> k = length ys - 1"
      proof (rule, rule, rule, simp)
        fix j k
        assume 2: "j < length xs" "k < length ys" "xs ! j = ys ! k"
        show "j = length xs - Suc 0 \<or> k = length ys - Suc 0"
        proof (rule ccontr, simp)
          assume 3: "j \<noteq> length xs - Suc 0 \<and> k \<noteq> length ys - Suc 0"
          let ?x' = "xs ! j"
          let ?y' = "ys ! k"
          from 2(1) 3 have "?x' \<in> set (butlast xs)" by - (rule butlast_idx', auto)
          moreover from 2(2) 3 have "?y' \<in> set (butlast ys)" by - (rule butlast_idx', auto)
          ultimately have "?x' \<noteq> ?y'" using 1 by simp
          with 2(3) show False by simp
        qed
      qed
    qed
    thus ?thesis by (auto simp:pathsConverge_def pathsConverge'_def)
  qed

  lemma pathsConvergeI:
    assumes "x\<comment>xs\<rightarrow>z" "y\<comment>ys\<rightarrow>z" "length xs > 1" "length ys > 1" "set (butlast xs) \<inter> set (butlast ys) = {}"
    shows "pathsConverge x xs y ys z"
  proof-
    from assms have "x \<noteq> y"
      by (metis append_is_Nil_conv disjoint_iff_not_equal length_butlast list.collapse list.distinct(1) nth_Cons_0 nth_butlast nth_mem path2_def split_list zero_less_diff)
    with assms show ?thesis by (simp add:pathsConverge'_def)
  qed
end

text {* A (control) flow graph G is reducible iff for each cycle C of G there is a node of C that dominates all other nodes in C. *}
definition (in graph_Entry) "reducible \<equiv> \<forall>n ns. n\<comment>ns\<rightarrow>n \<longrightarrow> (\<exists>m \<in> set ns. \<forall>n \<in> set ns. dominates m n)"

context CFG_SSA_Transformed
begin
  text {* A $\phi$ function for variable v is necessary in block Z iff two non-null paths $X \rightarrow^+ Z$ and $Y \rightarrow^+ Z$ converge at a block Z,
    such that the blocks X and Y contain assignments to v. *}
  definition "necessaryPhi v z \<equiv> \<exists>n ns m ms. pathsConverge n ns m ms z \<and> v \<in> oldDefs n \<and> v \<in> oldDefs m"
  abbreviation "necessaryPhi' val \<equiv> necessaryPhi (var val) (defNode val)"
  definition "unnecessaryPhi val \<equiv> phi val \<noteq> None \<and> \<not>necessaryPhi' val"

  lemma necessaryPhiI: "pathsConverge n ns m ms z \<Longrightarrow> v \<in> oldDefs n \<Longrightarrow> v \<in> oldDefs m \<Longrightarrow> necessaryPhi v z"
    by (auto simp: necessaryPhi_def)

  text {* A program with only necessary $\phi$ functions is in minimal SSA form. *}
  definition "cytronMinimal \<equiv> \<forall>v \<in> allVars. phi v \<noteq> None \<longrightarrow> necessaryPhi' v"

  text {* Let p be a $\phi$ function in a block P. Furthermore, let q in a block Q
and r in a block R be two operands of p, such that p, q and r are pairwise distinct.
Then at least one of Q and R does not dominate P. *}
  lemma 2:
    assumes "phiArg p q" "phiArg p r" "distinct [p, q, r]" and[simp]: "p \<in> allVars"
    shows "\<not>(def_dominates q p \<and> def_dominates r p)"
  proof (rule, erule conjE)
    txt {* Proof. Assume that Q and R dominate P, i.e., every path from the start block to P contains Q and R. *}
    assume asm: "def_dominates q p" "def_dominates r p"

    txt {*  Since immediate dominance forms a tree, Q dominates R or R dominates Q. *}
    hence "def_dominates q r \<or> def_dominates r q"
      by - (rule dominates_antitrans[of "defNode q" "defNode p" "defNode r"], auto)
    moreover
    {
      txt {*  Without loss of generality, let Q dominate R. *}
      fix q r
      assume assms: "phiArg p q" "phiArg p r" "distinct [p, q, r]"
      assume asm: "def_dominates q p" "def_dominates r p"
      assume wlog: "def_dominates q r"

      have[simp]: "var q = var r" using phiArg_same_var[OF assms(1)] phiArg_same_var[OF assms(2)] by simp

      txt {*  Furthermore, let S be the corresponding predecessor block of P where p is using q. *}
      obtain S where S: "q \<in> phiUses S" "S \<in> set (predecessors (defNode p))" by (rule phiUses_exI'[OF assms(1)], simp)

      txt {* Then there is a path from the start block crossing Q then R and S. *}
      have "defNode p \<noteq> defNode q" using assms(1,3)
        by - (rule phiArg_distinct_nodes, auto)
      with S have "dominates (defNode q) S"
        by - (rule allUses_dominated, auto)
      then obtain ns where ns: "defNode q\<comment>ns\<rightarrow>S" "distinct ns"
        by (rule dominates_path, auto elim: simple_path2)
      moreover have "defNode r \<in> set (tl ns)"
      proof-
        have "defNode r \<noteq> defNode q" using assms
          by - (rule phiArgs_def_distinct, auto)
        hence "hd ns \<noteq> defNode r" using ns by (auto simp:path2_def)
        moreover
        have "defNode p \<noteq> defNode r" using assms(2,3)
          by - (rule phiArg_distinct_nodes, auto)
        with S(2) have "dominates (defNode r) S"
          by - (rule dominates_unsnoc[where m="defNode p"], auto simp:wlog asm assms)
        with wlog have "defNode r \<in> set ns" using ns(1)
          by (rule dominates_mid)
        ultimately
        show ?thesis by (metis append_Nil in_set_conv_decomp list.sel(1) tl_append2)
      qed

      txt {* This violates the SSA property. *}
      moreover have "q \<in> allDefs (defNode q)" using assms S(1) by simp
      moreover have "r \<in> allDefs (defNode r)" using assms S(1) by simp
      ultimately have "var r \<noteq> var q" using S(1)
        by - (rule conventional, auto simp:path2_def distinct_hd_tl)
      hence False by simp
    }
    ultimately show False using assms asm by auto
  qed

  lemma convergence_prop:
    assumes "necessaryPhi (var v) n" "n\<comment>ns\<rightarrow>m" "v \<in> allUses m" "\<And>x. x \<in> set (tl ns) \<Longrightarrow> v \<notin> allDefs x" "v \<notin> defs n"
    shows "phis (n,v) \<noteq> None"
  proof
    from assms(2, 3) have "v \<in> allVars" by auto
    hence 1: "v \<in> allDefs (defNode v)" by (rule defNode)

    assume "phis (n,v) = None"
    with assms(5) have 2: "v \<notin> allDefs n"
      by (auto simp:allDefs_def phiDefs_def)

    from assms(1) obtain a as b bs v\<^sub>a v\<^sub>b where
      a: "v\<^sub>a \<in> defs a" "var v\<^sub>a = var v" and
      b: "v\<^sub>b \<in> defs b" "var v\<^sub>b = var v"
      and conv: "a\<comment>as\<rightarrow>n" "b\<comment>bs\<rightarrow>n" "1 < length as" "1 < length bs" "a \<noteq> b" "set (butlast as) \<inter> set (butlast bs) = {}"
      by (auto simp:necessaryPhi_def pathsConverge'_def oldDefs_def)
    have "dominates (defNode v) m" using assms(2,3)
      by - (rule allUses_dominated, auto)
    hence dom: "dominates (defNode v) n" using assms(2,4) 1
      by - (rule dominates_unsnoc', auto)
    hence "strict_dom (defNode v) n" using 1 2 by auto

    {
      fix v\<^sub>a a as v\<^sub>b b bs
      assume a: "v\<^sub>a \<in> defs a" "var v\<^sub>a = var v"
      assume as: "a\<comment>as\<rightarrow>n" "length as > 1"
      assume b: "v\<^sub>b \<in> defs b" "var v\<^sub>b = var v"
      assume bs: "b\<comment>bs\<rightarrow>n"
      assume conv: "a \<noteq> b" "set (butlast as) \<inter> set (butlast bs) = {}"
      have 3: "defNode v \<noteq> a"
      proof
        assume contr: "defNode v = a"

        have "a \<in> set (butlast as)" using as by (auto simp:path2_def intro:hd_in_butlast)
        hence "a \<notin> set (butlast bs)" using conv(2) by auto
        moreover
        have "a \<noteq> n" using 1 2 contr by auto
        hence "a \<noteq> last bs" using bs by (auto simp:path2_def)
        ultimately have 4: "a \<notin> set bs"
          by - (subst append_butlast_last_id[symmetric], rule path2_not_Nil[OF bs], auto)

        have "v \<noteq> v\<^sub>a"
        proof
          assume asm: "v = v\<^sub>a"
          have "v \<noteq> v\<^sub>b"
          proof
            assume "v = v\<^sub>b"
            with asm[symmetric] b(1) have "v\<^sub>a \<in> allDefs b" by auto
            with asm have "a = b" using as bs a(1) by - (rule allDefs_disjoint', auto)
            with conv(1) show False by simp
          qed
          obtain ebs where ebs: "Entry\<comment>ebs\<rightarrow>b"
            using bs by (atomize, auto)
          hence "Entry\<comment>butlast ebs@bs\<rightarrow>n" using bs by auto
          hence 5: "a \<in> set (butlast ebs@bs)"
            by - (rule dominatesE[OF dom[simplified contr]])
          show False
          proof (cases "a \<in> set (butlast ebs)")
            case True
            hence "a \<in> set ebs" by (rule in_set_butlastD)
            with ebs obtain abs where abs: "a\<comment>abs\<rightarrow>b" "a \<notin> set (tl abs)"
              by (rule path2_split_first_last, auto)
            let ?path = "(abs@tl bs)@tl ns"
            have "var v\<^sub>b \<noteq> var v\<^sub>a"
            proof (rule conventional)
              show "a\<comment>?path\<rightarrow>m" using abs(1) bs assms(2)
                by - (rule path2_app, rule path2_app)
              have "a \<notin> set (tl bs)" using 4 by (auto simp:in_set_tlD)
              moreover have "a \<notin> set (tl ns)" using 1 2 contr assms(4) by auto
              ultimately show "a \<notin> set (tl ?path)" using abs conv(2)
                by - (subst tl_append2, auto simp: path2_not_Nil)
              show "v\<^sub>a \<in> allUses m" using asm assms(3) by simp
              have "b \<in> set (tl abs)" using abs(1) conv(1)
                by (auto simp:path2_def intro!:last_in_tl nonsimple_length_gt_1)
              thus "b \<in> set (tl ?path)" using abs(1) by (simp add: path2_not_Nil)
            qed (auto simp: a b)
            thus False using a b by simp
          next
            case False
            with 4 5 show False by simp
          qed
        qed
        hence "var v \<noteq> var v\<^sub>a" using a as 1 contr by - (rule allDefs_var_disjoint[of a], auto)
        with a(2) show False by simp
      qed
      obtain eas where eas: "Entry\<comment>eas\<rightarrow>a"
        using as by (atomize, auto)
      hence "Entry\<comment>eas@tl as\<rightarrow>n" using as by auto
      hence 4: "defNode v \<in> set (eas@tl as)" by - (rule dominatesE[OF dom])

      have "defNode v \<in> set (tl as)"
      proof (rule ccontr)
        assume asm: "defNode v \<notin> set (tl as)"
        with 4 have "defNode v \<in> set eas" by simp
        then obtain eas' where eas': "defNode v\<comment>defNode v#eas'\<rightarrow>a" "defNode v \<notin> set eas'" using eas
          by - (rule path2_split_first_last)
        let ?path = "((defNode v#eas')@tl as)@tl ns"
        have "var v\<^sub>a \<noteq> var v"
        proof (rule conventional)
          show "defNode v\<comment>?path\<rightarrow>m" using eas' as assms(2)
            by (auto simp del:append_Cons append_assoc intro: path2_app)
          show "a \<in> set (tl ?path)" using eas' 3 by (auto simp:path2_def)
          show "defNode v \<notin> set (tl ?path)" using assms(4) 1 eas'(2) asm by auto
        qed (auto simp:1 assms(3) a(1))
        with a(2) show False by simp
      qed
      moreover have "defNode v \<noteq> n" using 1 2 by auto
      ultimately have "defNode v \<in> set (butlast as)" using as subsetD[OF set_tl, of "defNode v" as]
        by - (rule in_set_butlastI, auto simp:path2_def)
    }
    note def_in_as = this
    from def_in_as[OF a conv(1,3) b conv(2)] def_in_as[OF b conv(2,4) a conv(1)] conv(5,6) show False by auto
  qed

  lemma convergence_prop':
    assumes "necessaryPhi v n" "n\<comment>ns\<rightarrow>m" "v \<in> var ` allUses m" "\<And>x. x \<in> set ns \<Longrightarrow> v \<notin> oldDefs x"
    obtains val where "var val = v" "phis (n,val) \<noteq> None"
  using assms proof (induction "length ns" arbitrary: ns m rule: less_induct)
    case less
    from less.prems(4) obtain val where val: "var val = v" "val \<in> allUses m" by auto
    show ?thesis
    proof (cases "\<exists>m' \<in> set (tl ns). v \<in> var ` phiDefs m'")
      case False
      with less.prems(5) have "\<And>x. x \<in> set (tl ns) \<Longrightarrow> val \<notin> allDefs x"
        by (auto simp: allDefs_def val(1)[symmetric] oldDefs_def dest: in_set_tlD)
      moreover from less.prems(3,5) have "val \<notin> defs n"
        by (auto simp: oldDefs_def val(1)[symmetric] dest: path2_hd_in_ns)
      ultimately show ?thesis
        using less.prems
        by - (rule that[OF val(1)], rule convergence_prop, auto simp: val)
    next
      case True
      with less.prems(3) obtain ns' m' where m': "n\<comment>ns'\<rightarrow>m'" "v \<in> var ` phiDefs m'" "prefixeq ns' ns"
        by - (erule path2_split_first_prop[where P="\<lambda>m. v \<in> var ` phiDefs m"], auto dest: in_set_tlD)
      show ?thesis
      proof (cases "m' = n")
        case True
        with m'(2) show ?thesis by (auto simp: phiDefs_def intro: that)
      next
        case False
        with m'(1) obtain m'' where m'': "n\<comment>butlast ns'\<rightarrow>m''" "m'' \<in> set (predecessors m')"
          by - (rule path2_unsnoc, auto)
        show ?thesis
        proof (rule less.hyps[of "butlast ns'", OF _])
          show "length (butlast ns') < length ns"
            using m''(1) m'(3) by (cases "length ns'", auto dest: prefixeq_length_le)

          from m'(2) obtain val vs where vs: "phis (m',val) = Some vs" "var val = v"
            by (auto simp: phiDefs_def)
          with m'' obtain val' where "val' \<in> phiUses m''" "val' \<in> set vs"
            by - (rule phiUses_exI, auto simp: phiDefs_def)
          with vs have "val' \<in> allUses m''" "var val' = v" by auto
          then show "v \<in> var ` allUses m''" by auto

          from m'(3) show "\<And>x. x \<in> set (butlast ns') \<Longrightarrow> v \<notin> oldDefs x"
            by - (rule less.prems(5), auto elim: in_set_butlastD)
        qed (auto intro: less.prems(1,2) m''(1))
      qed
    qed
  qed

  lemma nontrivialE:
    assumes "\<not>trivial p" "phi p \<noteq> None" and[simp]: "p \<in> allVars"
    obtains r s where "phiArg p r" "phiArg p s" "distinct [p, r, s]"
  proof-
    from assms(2) obtain vs where vs: "phi p = Some vs" by auto
    have "card (set vs - {p}) \<ge> 2"
    proof-
      have "card (set vs) \<noteq> 0" using Entry_no_phis[of p] phi_wf[OF vs] vs by (auto simp:phi_def)
      moreover have "set vs \<noteq> {p}" using vs by - (rule phi_no_closed_loop, auto)
      ultimately have "card (set vs - {p}) \<noteq> 0"
        by (metis List.finite_set card_0_eq insert_Diff_single insert_absorb removeAll_id set_removeAll)
      moreover have "card (set vs - {p}) \<noteq> 1"
      proof
        assume "card (set vs - {p}) = 1"
        then obtain q where q: "{q} = set vs - {p}" by - (erule card_eq_1_singleton, auto)
        hence "isTrivialPhi p q" using vs by (auto simp:isTrivialPhi_def split:option.split)
        moreover have "phiArg p q" using q vs unfolding phiArg_def by auto
        ultimately show False using assms(1) by (auto simp:trivial_def)
      qed
      ultimately show ?thesis by arith
    qed
    then obtain r s where rs: "r \<noteq> s" "r \<in> set vs - {p}" "s \<in> set vs - {p}" by (rule set_take_two)
    thus ?thesis using vs by - (rule that[of r s], auto simp: phiArg_def)
  qed

  lemma paths_converge_prefix:
    assumes "x\<comment>xs\<rightarrow>z" "y\<comment>ys\<rightarrow>z" "x \<noteq> y" "length xs > 1" "length ys > 1" "x \<notin> set (butlast ys)" "y \<notin> set (butlast xs)"
    obtains xs' ys' z' where "pathsConverge x xs' y ys' z'" "prefixeq xs' xs" "prefixeq ys' ys"
  using assms proof (induction "length xs" arbitrary:xs ys z rule:nat_less_induct)
    case 1
    from "1.prems"(3,4) have 2: "x \<noteq> y" by (auto simp:path2_def)
    show thesis
    proof (cases "set (butlast xs) \<inter> set (butlast ys) = {}")
      case True
      with "1.prems"(2-) have "pathsConverge x xs y ys z" by (auto simp add: pathsConverge'_def)
      thus thesis by (rule "1.prems"(1), simp_all)
    next
      case False
      then obtain xs' z' where xs': "x\<comment>xs'\<rightarrow>z'" "prefixeq xs' (butlast xs)" "z' \<in> set (butlast ys)" "\<forall>a \<in> set (butlast xs'). a \<notin> set (butlast ys)"
        using "1.prems"(2,5) by - (rule path2_split_first_prop[of x "butlast xs" _ "\<lambda>a. a \<in> set (butlast ys)"], auto elim: path2_unsnoc)
      from xs'(3) "1.prems"(3) obtain ys' where ys': "y\<comment>ys'\<rightarrow>z'" "prefix ys' ys"
        by - (rule path2_strict_prefix_ex)
      show ?thesis
      proof (rule "1.hyps"[rule_format, OF _ _ _ xs'(1) ys'(1) assms(3)])
        show "length xs' < length xs" using xs'(2) xs'(1)
          by - (rule prefixeq_length_less, rule strict_prefix_butlast, auto)
        from "1.prems"(1) prefix_order.dual_order.strict_implies_order prefix_order.dual_order.trans
          prefixeq_butlastD xs'(2) ys'(2)
        show "\<And>xs'' ys'' z''. pathsConverge x xs'' y ys'' z'' \<Longrightarrow> prefixeq xs'' xs' \<Longrightarrow> prefixeq ys'' ys' \<Longrightarrow> thesis"
          by blast
        show "length xs' > 1"
        proof-
          have "length xs' \<noteq> 0" using xs' by auto
          moreover {
            assume "length xs' = 1"
            with xs'(1,3) have "x \<in> set (butlast ys)"
              by (auto simp:path2_def simp del:One_nat_def dest!:singleton_list_hd_last)
            with "1.prems"(7) have False ..
          }
          ultimately show ?thesis by arith
        qed

        show "length ys' > 1"
        proof-
          have "length ys' \<noteq> 0" using ys' by auto
          moreover {
            assume "length ys' = 1"
            with ys'(1) xs'(1,2) have "y \<in> set (butlast xs)"
              by (auto simp:path2_def path_not_Nil simp del:One_nat_def dest!:singleton_list_hd_last)
            with "1.prems"(8) have False ..
          }
          ultimately show ?thesis by arith
        qed

        show "y \<notin> set (butlast xs')"
          using  xs'(2) "1.prems"(8)
          by (metis in_prefix in_set_butlastD)
        show "x \<notin> set (butlast ys')"
          by (metis "1.prems"(7) in_set_butlast_appendI prefixE' ys'(2))
      qed simp
    qed
  qed

  lemma ununnecessaryPhis_disjoint_paths_aux:
    assumes "\<not>unnecessaryPhi r" and[simp]: "r \<in> allVars"
    obtains n\<^sub>1 ns\<^sub>1 n\<^sub>2 ns\<^sub>2 where
      "var r \<in> oldDefs n\<^sub>1" "n\<^sub>1\<comment>ns\<^sub>1\<rightarrow>defNode r" and
      "var r \<in> oldDefs n\<^sub>2" "n\<^sub>2\<comment>ns\<^sub>2\<rightarrow>defNode r" and
      "set (butlast ns\<^sub>1) \<inter> set (butlast ns\<^sub>2) = {}"
  proof (cases "phi r")
    case None
    thus thesis by - (rule that[of "defNode r" _ "defNode r"], auto intro!: oldDefsI intro: defNode_cases[of r])
  next
    case Some
    with assms that show ?thesis by (auto simp: unnecessaryPhi_def necessaryPhi_def pathsConverge'_def)
  qed

  lemma ununnecessaryPhis_disjoint_paths:
    assumes "\<not>unnecessaryPhi r" "\<not>unnecessaryPhi s"
      and rs: "phiArg p r" "phiArg p s" "distinct [p, r, s]"
      and[simp]: "var r = var p" "var s = var p" "p \<in> allVars"
    obtains n ns m ms where "var p \<in> oldDefs n" "n\<comment>ns\<rightarrow>defNode r" and "var p \<in> oldDefs m" "m\<comment>ms\<rightarrow>defNode s"
        and "set ns \<inter> set ms = {}"
  proof-
    from rs have[simp]: "r \<in> allVars" "s \<in> allVars" by auto

    obtain n\<^sub>1 ns\<^sub>1 n\<^sub>2 ns\<^sub>2 where
      ns\<^sub>1: "var p \<in> oldDefs n\<^sub>1" "n\<^sub>1\<comment>ns\<^sub>1\<rightarrow>defNode r" "defNode r \<notin> set (butlast ns\<^sub>1)" and
      ns\<^sub>2: "var p \<in> oldDefs n\<^sub>2" "n\<^sub>2\<comment>ns\<^sub>2\<rightarrow>defNode r" "defNode r \<notin> set (butlast ns\<^sub>2)" and
      ns: "set (butlast ns\<^sub>1) \<inter> set (butlast ns\<^sub>2) = {}"
    proof-
      from assms obtain n\<^sub>1 ns\<^sub>1 n\<^sub>2 ns\<^sub>2 where
        ns\<^sub>1: "var p \<in> oldDefs n\<^sub>1" "n\<^sub>1\<comment>ns\<^sub>1\<rightarrow>defNode r" and
        ns\<^sub>2: "var p \<in> oldDefs n\<^sub>2" "n\<^sub>2\<comment>ns\<^sub>2\<rightarrow>defNode r" and
        ns: "set (butlast ns\<^sub>1) \<inter> set (butlast ns\<^sub>2) = {}"
      by - (rule ununnecessaryPhis_disjoint_paths_aux, auto)

      from ns\<^sub>1 obtain ns\<^sub>1' where ns\<^sub>1': "n\<^sub>1\<comment>ns\<^sub>1'\<rightarrow>defNode r" "defNode r \<notin> set (butlast ns\<^sub>1')" "distinct ns\<^sub>1'" "set ns\<^sub>1' \<subseteq> set ns\<^sub>1"
        by (auto elim: simple_path2)
      from ns\<^sub>2 obtain ns\<^sub>2' where ns\<^sub>2': "n\<^sub>2\<comment>ns\<^sub>2'\<rightarrow>defNode r" "defNode r \<notin> set (butlast ns\<^sub>2')" "distinct ns\<^sub>2'" "set ns\<^sub>2' \<subseteq> set ns\<^sub>2"
        by (auto elim: simple_path2)

      have "set (butlast ns\<^sub>1') \<inter> set (butlast ns\<^sub>2') = {}"
      proof (rule equals0I)
        fix x
        assume 1: "x \<in> set (butlast ns\<^sub>1') \<inter> set (butlast ns\<^sub>2')"
        with set_butlast_distinct[OF ns\<^sub>1'(3)] ns\<^sub>1'(1) have 2: "x \<noteq> defNode r" by (auto simp:path2_def)
        with 1 ns\<^sub>1'(4) ns\<^sub>2'(4) ns\<^sub>1(2) ns\<^sub>2(2) have "x \<in> set (butlast ns\<^sub>1)" "x \<in> set (butlast ns\<^sub>2)"
          by - (auto intro!:in_set_butlastI elim:in_set_butlastD simp:path2_def)
        with ns show False by auto
      qed

      thus thesis by (rule that[OF ns\<^sub>1(1) ns\<^sub>1'(1,2) ns\<^sub>2(1) ns\<^sub>2'(1,2)])
    qed

    obtain m ms where ms: "var p \<in> oldDefs m" "m\<comment>ms\<rightarrow>defNode s" "defNode r \<notin> set ms"
    proof-
      from assms(2) obtain m\<^sub>1 ms\<^sub>1 m\<^sub>2 ms\<^sub>2 where
        ms\<^sub>1: "var p \<in> oldDefs m\<^sub>1" "m\<^sub>1\<comment>ms\<^sub>1\<rightarrow>defNode s" and
        ms\<^sub>2: "var p \<in> oldDefs m\<^sub>2" "m\<^sub>2\<comment>ms\<^sub>2\<rightarrow>defNode s" and
        ms: "set (butlast ms\<^sub>1) \<inter> set (butlast ms\<^sub>2) = {}"
        by - (rule ununnecessaryPhis_disjoint_paths_aux, auto)
      show thesis
      proof (cases "defNode r \<in> set ms\<^sub>1")
        case False
        with ms\<^sub>1 show thesis by (rule that)
      next
        case True
        have "defNode r \<notin> set ms\<^sub>2"
        proof
          assume "defNode r \<in> set ms\<^sub>2"
          moreover from rs have "defNode r \<noteq> defNode s"
            by - (rule phiArgs_def_distinct, auto)
          ultimately have "defNode r \<in> set (butlast ms\<^sub>1)" "defNode r \<in> set (butlast ms\<^sub>2)" using True ms\<^sub>1(2) ms\<^sub>2(2)
            by (auto simp:path2_def intro:in_set_butlastI)
          with ms show False by auto
        qed
        with ms\<^sub>2 show thesis by (rule that)
      qed
    qed

    show ?thesis
    proof (cases "(set ns\<^sub>1 \<union> set ns\<^sub>2) \<inter> set ms = {}")
      case True
      with ns\<^sub>1 ms show ?thesis by - (rule that, auto)
    next
      case False
      then obtain m' ms' where ms': "m'\<comment>ms'\<rightarrow>defNode s" "m' \<in> set ns\<^sub>1 \<union> set ns\<^sub>2" "set (tl ms') \<inter> (set ns\<^sub>1 \<union> set ns\<^sub>2) = {}" "suffixeq ms' ms"
        by - (rule path2_split_last_prop[OF ms(2), of "\<lambda>x. x \<in> set ns\<^sub>1 \<union> set ns\<^sub>2"], auto)
      from this(4) ms(3) have 2: "defNode r \<notin> set ms'"
        by (auto dest:suffixeq_set_subset)
      {
        fix n\<^sub>1 ns\<^sub>1 n\<^sub>2 ns\<^sub>2
        assume 4: "m' \<in> set ns\<^sub>1"
        assume ns\<^sub>1: "var p \<in> oldDefs n\<^sub>1" "n\<^sub>1\<comment>ns\<^sub>1\<rightarrow>defNode r" "defNode r \<notin> set (butlast ns\<^sub>1)"
        assume ns\<^sub>2: "var p \<in> oldDefs n\<^sub>2" "n\<^sub>2\<comment>ns\<^sub>2\<rightarrow>defNode r" "defNode r \<notin> set (butlast ns\<^sub>2)"
        assume ns: "set (butlast ns\<^sub>1) \<inter> set (butlast ns\<^sub>2) = {}"
        assume ms': "m'\<comment>ms'\<rightarrow>defNode s" "set (tl ms') \<inter> (set ns\<^sub>1 \<union> set ns\<^sub>2) = {}"
        have "m' \<in> set (butlast ns\<^sub>1)"
        proof-
          from ms'(1) have "m' \<in> set ms'" by auto
          with 2 have "defNode r \<noteq> m'" by auto
          with 4 ns\<^sub>1(2) show ?thesis by - (rule in_set_butlastI, auto simp:path2_def)
        qed
        with ns\<^sub>1(2) obtain ns\<^sub>1' where ns\<^sub>1': "n\<^sub>1\<comment>ns\<^sub>1'\<rightarrow>m'" "m' \<notin> set (butlast ns\<^sub>1')" "prefix ns\<^sub>1' ns\<^sub>1"
          by - (rule path2_strict_prefix_ex)
        have thesis
        proof (rule that[OF ns\<^sub>2(1,2), OF ns\<^sub>1(1), of "ns\<^sub>1'@tl ms'"])
          show "n\<^sub>1\<comment>ns\<^sub>1' @ tl ms'\<rightarrow>defNode s" using ns\<^sub>1'(1) ms'(1) by auto
          show "set ns\<^sub>2 \<inter> set (ns\<^sub>1' @ tl ms') = {}"
          proof (rule equals0I)
            fix x
            assume x: "x \<in> set ns\<^sub>2 \<inter> set (ns\<^sub>1' @ tl ms')"
            show False
            proof (cases "x \<in> set ns\<^sub>1'")
              case True
              hence 4: "x \<in> set (butlast ns\<^sub>1)" using ns\<^sub>1'(3) by (auto dest:set_mono_prefix)
              with ns\<^sub>1(3) have "x \<noteq> defNode r" by auto
              with ns\<^sub>2(2) x have "x \<in> set (butlast ns\<^sub>2)"
                by - (rule in_set_butlastI, auto simp:path2_def)
              with 4 ns show False by auto
            next
              case False
              with x have "x \<in> set (tl ms')" by simp
              with x ms'(2) show False by auto
            qed
          qed
        qed
      }
      note 4 = this
      show ?thesis
      proof (cases "m' \<in> set ns\<^sub>1")
        case True
        thus ?thesis using ns\<^sub>1 ns\<^sub>2 ns ms'(1,3) by (rule 4)
      next
        case False
        with ms'(2) have "m' \<in> set ns\<^sub>2" by simp
        thus ?thesis using ns ms'(1,3) by - (rule 4[OF _ ns\<^sub>2 ns\<^sub>1], auto)
      qed
    qed
  qed

  text {* Lemma 3. If a $\phi$ function p in a block P for a variable v is unnecessary, but non-trivial, then it has an operand q in a block Q,
    such that q is an unnecessary $\phi$ function and Q does not dominate P.*}
  lemma 3:
    assumes "unnecessaryPhi p" "\<not>trivial p" and[simp]: "p \<in> allVars"
    obtains q where "phiArg p q" "unnecessaryPhi q" "\<not>def_dominates q p"
  proof-
    note unnecessaryPhi_def[simp]
    let ?P = "defNode p"

    txt {* The node p must have at least two different operands r and s, which are not p itself. Otherwise, p is trivial. *}
    from assms obtain r s where rs: "phiArg p r" "phiArg p s" "distinct [p, r, s]"
      by - (rule nontrivialE, auto)
    hence[simp]: "var r = var p" "var s = var p" "r \<in> allVars" "s \<in> allVars"
      by (simp_all add:phiArg_same_var)

    txt {* They can either be:
– The result of a direct assignment to v.
– The result of a necessary $\phi$ function r' . This however means that r' was
reachable by at least two different direct assignments to v. So there is a path
from a direct assignment of v to p.
– Another unnecessary $\phi$ function. *}

    let ?R = "defNode r"
    let ?S = "defNode s"

    have[simp]: "?R \<noteq> ?S" using rs by - (rule phiArgs_def_distinct, auto)

    have one_unnec: "unnecessaryPhi r \<or> unnecessaryPhi s"
    proof (rule ccontr, simp only: de_Morgan_disj not_not)

      txt {* Assume neither r in a block R nor s in a block S is an unnecessary $\phi$ function. *}
      assume asm: "\<not>unnecessaryPhi r \<and> \<not>unnecessaryPhi s"

      txt {* Then a path from an assignment to v in a block n crosses R and a path from an assignment to v in a block m crosses S. *}
      txt {* AMENDMENT: ...so that the paths are disjoint! *}
      obtain n ns m ms where ns: "var p \<in> oldDefs n" "n\<comment>ns\<rightarrow>?R" "n \<notin> set (tl ns)"
        and ms: "var p \<in> oldDefs m" "m\<comment>ms\<rightarrow>defNode s" "m \<notin> set (tl ms)"
        and ns_ms: "set ns \<inter> set ms = {}"
      proof-
        obtain n ns m ms where ns: "var p \<in> oldDefs n" "n\<comment>ns\<rightarrow>?R" and ms: "var p \<in> oldDefs m" "m\<comment>ms\<rightarrow>?S"
          and ns_ms: "set ns \<inter> set ms = {}"
          using asm[THEN conjunct1] asm[THEN conjunct2] rs by (rule ununnecessaryPhis_disjoint_paths, auto)
        moreover from ns obtain ns' where "n\<comment>ns'\<rightarrow>?R" "n \<notin> set (tl ns')" "set ns' \<subseteq> set ns"
          by (auto intro: simple_path2)
        moreover from ms obtain ms' where "m\<comment>ms'\<rightarrow>?S" "m \<notin> set (tl ms')" "set ms' \<subseteq> set ms"
          by (auto intro: simple_path2)
        ultimately show thesis by - (rule that[of n ns' m ms'], auto)
      qed

      from ns(1) ms(1) obtain v v' where v: "v \<in> defs n" and v': "v' \<in> defs m" and[simp]: "var v = var p" "var v' = var p"
        by (auto simp:oldDefs_def)

      txt {* They converge at P or earlier. *}
      obtain ns' n' where ns': "?R\<comment>ns'\<rightarrow>n'" "r \<in> phiUses n'" "n' \<in> set (predecessors ?P)" "?R \<notin> set (tl ns')"
        by (rule phiArg_path_ex'[OF rs(1)], auto elim: simple_path2)
      obtain ms' m' where ms': "?S\<comment>ms'\<rightarrow>m'" "s \<in> phiUses m'" "m' \<in> set (predecessors ?P)" "?S \<notin> set (tl ms')"
        by (rule phiArg_path_ex'[OF rs(2)], auto elim: simple_path2)

      let ?left = "(ns@tl ns')@[?P]"
      let ?right = "(ms@tl ms')@[?P]"

      obtain ns'' ms'' z where z: "pathsConverge n ns'' m ms'' z" "prefixeq ns'' ?left" "prefixeq ms'' ?right"
      proof (rule paths_converge_prefix)
        show "n \<noteq> m" using ns ms ns_ms by auto

        show "n\<comment>?left\<rightarrow>?P" using ns ns'
          by - (rule path2_snoc, rule path2_app)
        show "length ?left > 1" using ns by auto
        show "m\<comment>?right\<rightarrow>?P" using ms ms'
          by - (rule path2_snoc, rule path2_app)
        show "length ?right > 1" using ms by auto

        have "n \<notin> set ms" using ns_ms ns by auto
        moreover have "n \<notin> set (tl ms')" using v rs(2) ms'(2) asm
          by - (rule conventional'[OF ms'(1,4), of s v], auto)
        ultimately show "n \<notin> set (butlast ?right)"
          by (auto simp del:append_assoc)

        have "m \<notin> set ns" using ns_ms ms by auto
        moreover have "m \<notin> set (tl ns')" using v' rs(1) ns'(2) asm
          by - (rule conventional'[OF ns'(1,4), of r v'], auto)
        ultimately show "m \<notin> set (butlast ?left)"
          by (auto simp del:append_assoc)
      qed

      from this(1) ns(1) ms(1) have necessary: "necessaryPhi (var p) z" by (rule necessaryPhiI)

      show False
      proof (cases "z = ?P")

        txt {* Convergence at P is not possible because p is unnecessary. *}
        case True
        thus False using assms(1) necessary by simp
      next

        txt {* An earlier convergence would imply a necessary $\phi$ function at this point, which violates the SSA property. *}
        case False
        from z(1) have "z \<in> set ns'' \<inter> set ms''" by (auto simp: pathsConverge'_def)
        with False have "z \<in> set (ns@tl ns') \<inter> set (ms@tl ms')"
          using z(2,3)[THEN set_mono_prefixeq] by (auto elim:set_mono_prefixeq)
        hence z_on: "z \<in> set (tl ns') \<union> set (tl ms')" using ns_ms by auto

        {
          fix r ns' n'
          let ?R = "defNode r"
          assume ns': "?R\<comment>ns'\<rightarrow>n'" "r \<in> phiUses n'" "n' \<in> set (predecessors (?P))" "?R \<notin> set (tl ns')"
          assume rs: "var r = var p"
          have "z \<notin> set (tl ns')"
          proof
            assume asm: "z \<in> set (tl ns')"
            obtain zs where zs: "z\<comment>zs\<rightarrow>n'" "set (tl zs) \<subseteq> set (tl ns')" using asm
              by - (rule path2_split_ex[OF ns'(1)], auto simp: path2_not_Nil elim: subsetD[OF set_tl])

            have "phis (z, r) \<noteq> None"
            proof (rule convergence_prop[OF necessary[simplified rs[symmetric]] zs(1)])
              show "r \<in> allUses n'" using ns'(2) by auto
              show "r \<notin> defs z"
              proof
                assume "r \<in> defs z"
                hence "?R = z" using zs by - (rule defNode_eq, auto)
                thus False using ns'(4) asm by auto
              qed
            next
              fix x
              assume "x \<in> set (tl zs)"
              moreover have "?R \<notin> set (tl zs)" using ns'(4) zs(2) by auto
              ultimately show "r \<notin> allDefs x"
                by (metis defNode_eq path2_in_\<alpha>n set_tl subset_code(1) zs(1))
            qed
            hence "?R = z" using zs(1) by - (rule defNode_eq, auto simp:allDefs_def phiDefs_def)
            thus False using ns'(4) asm by auto
          qed
        }
        note z_not_on = this

        have "z \<notin> set (tl ns')" by (rule z_not_on[OF ns'], simp)
        moreover have "z \<notin> set (tl ms')" by (rule z_not_on[OF ms'], simp)
        ultimately show False using z_on by simp
      qed
    qed

    txt {*
So r or s must be an unnecessary $\phi$ function. Without loss of generality, let
this be r. *}
    {
      fix r s
      assume r: "unnecessaryPhi r" and[simp]: "var r = var p"
      assume[simp]: "var s = var p"
      assume rs: "phiArg p r" "phiArg p s" "distinct [p, r, s]"
      let ?R = "defNode r"
      let ?S = "defNode s"

      have[simp]: "?R \<noteq> ?S" using rs by - (rule phiArgs_def_distinct, auto)
      have[simp]: "s \<in> allVars" using rs by auto

      have thesis
      proof (cases "dominates ?R ?P")
        case False

        txt {* If R does not dominate P, then r is the sought-after q. *}
        thus thesis using r rs(1) by - (rule that)
      next
        case True

        txt {* So let R dominate P.
Due to Lemma 2, S does not dominate P. *}
        hence 4: "\<not>dominates ?S ?P" using 2[OF rs] by simp

        txt {* Employing the SSA property, r /= p
yields R /= P. *}
        (* actually not SSA property *)
        have "?R \<noteq> ?P"
        proof (rule notI, rule allDefs_var_disjoint[of ?R p r, simplified])
          show "r \<in> allDefs (defNode r)" using rs(1) by auto
          show "p \<noteq> r" using rs(3) by auto
        qed auto

        txt {* Thus, R strictly dominates P. *}
        hence "strict_dom ?R ?P" using True by simp

        txt {* This implies that R dominates all
predecessors of P, which contain the uses of p, especially the predecessor S' that
contains the use of s. *}
        moreover obtain ss' S' where ss': "?S\<comment>ss'\<rightarrow>S'"
          and S': "s \<in> phiUses S'" "S' \<in> set (predecessors ?P)"
          by (rule phiArg_path_ex'[OF rs(2)], simp)
        ultimately have 5: "dominates ?R S'" by - (rule dominates_unsnoc, auto)

        txt {* Due to the SSA property, there is a path from S to S' that
does not contain R. *}
        from ss' obtain ss' where ss': "?S\<comment>ss'\<rightarrow>S'" "?S \<notin> set (tl ss')" by (rule simple_path2)
        hence "?R \<notin> set (tl ss')" using rs(1,2) S'(1)
          by - (rule conventional'[where v=s and v'=r], auto simp del: phiArg_def)

        txt {* Employing R dominates S' this yields R dominates S. *}
        hence dom: "dominates ?R ?S" using 5 ss' by - (rule dominates_extend)

        txt {* Now assume that s is necessary. *}
        have "unnecessaryPhi s"
        proof (rule ccontr)
          assume s: "\<not>unnecessaryPhi s"

          txt {* Let X contain the most recent definition of v on a path from the start block to R. *}
          from rs(1) obtain X xs where xs: "X\<comment>xs\<rightarrow>?R" "var r \<in> oldDefs X" "EntryPath xs"
            by - (rule allDef_path_from_simpleDef[of r], auto simp del: phiArg_def)
          then obtain X xs where xs: "X\<comment>xs\<rightarrow>?R" "var r \<in> oldDefs X" "\<forall>x \<in> set (tl xs). var r \<notin> oldDefs x" "EntryPath xs"
            by - (rule path2_split_last_prop[OF xs(1), of "\<lambda>x. var r \<in> oldDefs x"], auto dest: EntryPath_suffixeq)
          then obtain x where x: "x \<in> defs X" "var x = var r" by (auto simp: oldDefs_def path2_def)
          hence[simp]: "X = defNode x" using xs by - (rule defNode_eq[symmetric], auto)
          from xs obtain xs where xs: "X\<comment>xs\<rightarrow>?R" "X \<notin> set (tl xs)" "EntryPath xs"
            by - (rule simple_path2, auto dest: EntryPath_suffixeq)

          txt {* By Definition 2 there are two definitions
of v that render s necessary. Since R dominates S, the SSA property yields that
one of these definitions is contained in a block Y on a path $R \rightarrow^+ S$. *}
          (* actually not SSA property *)
          obtain Y ys ys' where Y: "var s \<in> oldDefs Y"
            and ys: "Y\<comment>ys\<rightarrow>?S" "?R \<notin> set ys"
            and ys': "?R\<comment>ys'\<rightarrow>Y" "?R \<notin> set (tl ys')"
          proof (cases "phi s")
            case None
            hence "s \<in> defs ?S" by - (rule defNode_cases[of s], auto)
            moreover obtain ns where "?R\<comment>ns\<rightarrow>?S" "?R \<notin> set (tl ns)" using dom
              by - (rule dominates_path, auto intro: simple_path2)
            ultimately show thesis by - (rule that[where ys4="[?S]"], auto dest: oldDefsI)
          next
            case Some
            with s obtain Y\<^sub>1 ys\<^sub>1 Y\<^sub>2 ys\<^sub>2 where "var s \<in> oldDefs Y\<^sub>1" "Y\<^sub>1\<comment>ys\<^sub>1\<rightarrow>?S"
              and "var s \<in> oldDefs Y\<^sub>2" "Y\<^sub>2\<comment>ys\<^sub>2\<rightarrow>?S"
              and ys: "set (butlast ys\<^sub>1) \<inter> set (butlast ys\<^sub>2) = {}" "Y\<^sub>1 \<noteq> Y\<^sub>2"
              by (auto simp:necessaryPhi_def pathsConverge'_def)
            moreover from ys(1) have "?R \<notin> set (butlast ys\<^sub>1) \<or> ?R \<notin> set (butlast ys\<^sub>2)" by auto
            ultimately obtain Y ys where ys: "var s \<in> oldDefs Y" "Y\<comment>ys\<rightarrow>?S" "?R \<notin> set (butlast ys)" by auto
            obtain es where es: "Entry\<comment>es\<rightarrow>Y" using ys(2)
              by - (atomize_elim, rule Entry_reaches, auto)
            have "?R \<in> set (butlast es@ys)" using path2_app'[OF es ys(2)] by - (rule dominatesE[OF dom])
            moreover have "?R \<noteq> last ys" using path2_last[OF ys(2), symmetric] by simp
            hence 1: "?R \<notin> set ys" using ys(3) by (auto dest: in_set_butlastI)
            ultimately have "?R \<in> set (butlast es)" by auto
            then obtain ys' where "?R\<comment>ys'\<rightarrow>Y" "?R \<notin> set (tl ys')" using es
              by - (rule path2_split_ex, assumption, rule in_set_butlastD, auto intro: simple_path2)
            thus thesis using ys(1,2) 1 by - (rule that[of Y ys ys'], auto)
          qed

          from Y obtain y where y: "y \<in> defs Y" "var y = var s" by (auto simp: oldDefs_def)
          hence[simp]: "Y = defNode y" using ys by - (rule defNode_eq[symmetric], auto)

          obtain rr' R' where "?R\<comment>rr'\<rightarrow>R'"
            and R': "r \<in> phiUses R'" "R' \<in> set (predecessors ?P)"
            by (rule phiArg_path_ex'[OF rs(1)], simp)
          then obtain rr' where rr': "?R\<comment>rr'\<rightarrow>R'" "?R \<notin> set (tl rr')" by - (rule simple_path2)
          with R' obtain rr where rr: "?R\<comment>rr\<rightarrow>?P" and[simp]: "rr = rr' @ [?P]" by (auto intro: path2_snoc)
          from ss' S' obtain ss where ss: "?S\<comment>ss\<rightarrow>?P" and[simp]: "ss = ss' @ [?P]" by (auto intro: path2_snoc)

          txt {* Thus, there are paths $X \rightarrow^+ P$ and $Y \rightarrow^+ P$ rendering p necessary. Since this is a
contradiction, s is unnecessary and the sought-after q. *}
          have "pathsConverge X (butlast xs@rr) Y (ys@tl ss) ?P"
          proof (rule pathsConvergeI)
            show "X\<comment>butlast xs@rr\<rightarrow>?P" using xs rr by auto
            show "Y\<comment>ys@tl ss\<rightarrow>?P" using ys ss by auto

            {
              assume "X = ?P"
              moreover have "p \<in> phiDefs ?P" using assms(1) by (auto simp:phiDefs_def phi_def)
              ultimately have False using simpleDefs_phiDefs_disjoint[of X] allDefs_var_disjoint[of X] x by (cases "x = p", auto)
            }
            thus "length (butlast xs@rr) > 1" using xs rr by - (rule path2_nontriv, auto)

            {
              assume "Y = ?P"
              moreover have "p \<in> phiDefs ?P" using assms(1) by (auto simp:phiDefs_def phi_def)
              ultimately have False using simpleDefs_phiDefs_disjoint[of Y] allDefs_var_disjoint[of Y] y by (cases "y = p", auto)
            }
            thus "length (ys@tl ss) > 1" using ys ss by - (rule path2_nontriv, auto)
            show "set (butlast (butlast xs @rr)) \<inter> set (butlast (ys @ tl ss)) = {}"
            proof (rule equals0I)
              fix z
              assume "z \<in> set (butlast (butlast xs@rr)) \<inter> set (butlast (ys@tl ss))"
              moreover {
                assume asm: "z \<in> set (butlast xs)" "z \<in> set ys"
                have "shortestPath z < shortestPath ?R" using asm(1) xs(3)
                  by - (subst path2_last[OF xs(1)], rule EntryPath_butlast_less_last)
                moreover
                from ys asm(2) obtain ys' where ys': "z\<comment>ys'\<rightarrow>?S" "suffixeq ys' ys"
                  by - (rule path2_split_ex, auto simp: suffixeq_def)
                have "dominates ?R z" using ys(2) set_tl[of ys] suffixeq_tl_subset[OF ys'(2)]
                  by - (rule dominates_extend[OF dom ys'(1)], auto)
                hence "shortestPath ?R \<le> shortestPath z"
                  by (rule dominates_shortestPath_order, auto)
                ultimately have False by simp
              }
              moreover {
                assume asm: "z \<in> set (butlast xs)" "z \<in> set (tl ss')"
                have "shortestPath z < shortestPath ?R" using asm(1) xs(3)
                  by - (subst path2_last[OF xs(1)], rule EntryPath_butlast_less_last)
                moreover
                from asm(2) obtain ss\<^sub>2 where ss\<^sub>2: "z\<comment>ss\<^sub>2\<rightarrow>S'" "set (tl ss\<^sub>2) \<subseteq> set (tl ss')"
                  using set_tl[of ss'] by - (rule path2_split_ex[OF ss'(1)], auto simp: path2_not_Nil dest: in_set_butlastD)
                from S'(1) ss'(1) have "dominates ?S S'" by - (rule allUses_dominated, auto)
                hence "dominates ?S z" using ss'(2) ss\<^sub>2(2)
                  by - (rule dominates_extend[OF _ ss\<^sub>2(1)], auto)
                with dom have "dominates ?R z" by (rule dominates_trans)
                hence "shortestPath ?R \<le> shortestPath z"
                  by - (rule dominates_shortestPath_order, auto)
                ultimately have False by simp
              }
              moreover
              have "?R \<noteq> Y" using ys by (auto simp:path2_def)
              with ys'(1) have 1: "length ys' > 1" by (rule path2_nontriv)
              {
                assume asm: "z \<in> set rr'" "z \<in> set ys"
                then obtain ys\<^sub>1 where ys\<^sub>1: "Y\<comment>ys\<^sub>1\<rightarrow>z" "prefixeq ys\<^sub>1 ys"
                  by - (rule path2_split_ex[OF ys(1)], auto)
                from asm obtain rr\<^sub>2 where rr\<^sub>2: "z\<comment>rr\<^sub>2\<rightarrow>R'" "set (tl rr\<^sub>2) \<subseteq> set (tl rr')"
                  by - (rule path2_split_ex[OF rr'(1)], auto simp: path2_not_Nil)
                let ?path = "ys'@tl (ys\<^sub>1@tl rr\<^sub>2)"
                have "var y \<noteq> var r"
                proof (rule conventional)
                  show "?R\<comment>?path\<rightarrow>R'" using ys' ys\<^sub>1 rr\<^sub>2 by (intro path2_app)
                  show "r \<in> allDefs ?R" using rs by auto
                  show "r \<in> allUses R'" using R' by auto

                  thus "Y \<in> set (tl ?path)" using ys'(1) 1
                    by (auto simp:path2_def path2_not_Nil intro:last_in_tl)
                  show "y \<in> allDefs Y" using y by auto
                  show "defNode r \<notin> set (tl ?path)"
                    using ys' ys\<^sub>1(1) ys(2) rr\<^sub>2(2) rr'(2) prefixeq_tl_subset[OF ys\<^sub>1(2)] set_tl[of ys] by (auto simp: path2_not_Nil)
                qed
                hence False using y by simp
              }
              moreover {
                assume asm: "z \<in> set rr'" "z \<in> set (tl ss')"
                then obtain ss'\<^sub>1 where ss'\<^sub>1: "?S\<comment>ss'\<^sub>1\<rightarrow>z" "prefixeq ss'\<^sub>1 ss'" using ss'
                  by - (rule path2_split_ex[OF ss'(1), of z], auto)
                from asm obtain rr'\<^sub>2 where rr'\<^sub>2: "z\<comment>rr'\<^sub>2\<rightarrow>R'" "suffixeq rr'\<^sub>2 rr'"
                  using rr' by - (rule path2_split_ex, auto simp: suffixeq_def)
                let ?path = "butlast ys'@(ys@tl (ss'\<^sub>1@tl rr'\<^sub>2))"
                have "var s \<noteq> var r"
                proof (rule conventional)
                  show "?R\<comment>?path\<rightarrow>R'" using ys' ys ss'\<^sub>1 rr'\<^sub>2(1) by (intro path2_app path2_app')
                  show "r \<in> allDefs ?R" using rs by auto
                  show "r \<in> allUses R'" using R' by auto
                  from 1 have[simp]: "butlast ys' \<noteq> []" by (cases ys', auto)
                  show "?S \<in> set (tl ?path)" using ys(1) by auto
                  show "s \<in> allDefs ?S" using rs(2) by auto
                  have "?R \<notin> set (tl ss')"
                    using rs S'(1) by - (rule conventional''[OF ss'], auto)
                  thus "defNode r \<notin> set (tl ?path)"
                    using ys(1) ss'\<^sub>1(1) suffixeq_tl_subset[OF rr'\<^sub>2(2)] ys'(2) ys(2) rr'(2) prefixeq_tl_subset[OF ss'\<^sub>1(2)]
                    by (auto simp: List.butlast_tl[symmetric] path2_not_Nil dest: in_set_butlastD)
                qed
                hence False using y by simp
              }
              ultimately show False using rr'(1) ss'(1)
                by (auto simp del: append_assoc simp: append_assoc[symmetric] path2_not_Nil dest: in_set_tlD)
            qed
          qed
          hence "necessaryPhi' p" using xs oldDefsI[OF x(1)] x(2) oldDefsI[OF y(1)] y(2)
            by - (rule necessaryPhiI[where v="var p"], assumption, auto simp:path2_def)
          with assms(1) show False by auto
        qed
        thus ?thesis using rs(2) 4 by - (rule that)
      qed
    }
    from one_unnec this[of r s] this[of s r] rs show thesis by auto
  qed

text {* Theorem 1. A program in SSA form with a reducible CFG G without any trivial $\phi$ functions is in minimal SSA form. *}
  theorem reducible_nonredundant_imp_minimal:
    assumes "reducible" "\<not>redundant"
    shows "cytronMinimal"
  unfolding cytronMinimal_def
  proof (rule, rule)
    txt {*
Proof. Assume G is not in minimal SSA form and contains no trivial $\phi$ functions.
We choose an unnecessary $\phi$ function p. *}
    fix p
    assume[simp]: "p \<in> allVars" and phi: "phi p \<noteq> None"
    show "necessaryPhi' p"
    proof (rule ccontr)
      assume "\<not>necessaryPhi' p"
      with phi have asm: "unnecessaryPhi p" by (simp add: unnecessaryPhi_def)
      let ?A = "{p. p \<in> allVars \<and> unnecessaryPhi p}"
      let ?r = "\<lambda>p q. p \<in> ?A \<and> q \<in> ?A \<and> phiArg p q \<and> \<not>def_dominates q p"
      let ?r' = "{(p,q). ?r p q}"
      note phiArg_def[simp del]

      txt {*  Due to Lemma 3, p has an operand q,
which is unnecessary and does not dominate p. By induction q has an unnecessary
$\phi$ function as operand as well and so on. Since the program only has a finite
number of operations, there must be a cycle when following the q chain. *}
      obtain q where q: "(q,q) \<in> ?r'\<^sup>+" "q \<in> ?A"
      proof (rule serial_on_finite_cycle)
        show "serial_on ?A ?r'"
        proof (rule serial_onI)
          fix x
          assume "x \<in> ?A"
          then obtain y where "unnecessaryPhi y" "phiArg x y" "\<not>def_dominates y x"
            using assms(2) by - (rule 3, auto simp: redundant_def)
          thus "\<exists>y \<in> ?A. (x,y) \<in> ?r'" using `x \<in> ?A` by - (rule bexI[where x=y], auto)
        qed
        show "?A \<noteq> {}" using asm by (auto intro!: exI)
      qed auto

      txt {* A cycle in the $\phi$ functions implies a cycle in G. *}
      then obtain ns where ns: "defNode q\<comment>ns\<rightarrow>defNode q" "length ns > 1"
        "\<forall>n \<in> set (butlast ns). \<exists>p q m ns'. ?r p q \<and> defNode q\<comment>ns'\<rightarrow>m \<and> (defNode q) \<notin> set (tl ns') \<and> q \<in> phiUses m \<and> m \<in> set (predecessors (defNode p)) \<and> n \<in> set ns' \<and> set ns' \<subseteq> set ns \<and> defNode p \<in> set ns"
        by - (rule phiArg_tranclp_path_ex[where r="?r"], auto simp: tranclp_unfold)

      txt {* As G is reducible, the control flow
cycle contains one entry block, which dominates all other blocks in the cycle. *}
      obtain n where n: "n \<in> set ns" "\<forall>m \<in> set ns. dominates n m"
        using assms(1)[unfolded reducible_def, rule_format, OF ns(1)] by auto

      txt {* Without loss of generality, let q be in the entry block, which means it dominates p. *}
      have "n \<in> set (butlast ns)"
      proof (cases "n = last ns")
        case False
        with n(1) show ?thesis by (rule in_set_butlastI)
      next
        case True
        with ns(1) have "n = hd ns" by (auto simp: path2_def)
        with ns(2) show ?thesis by - (auto intro: hd_in_butlast)
      qed
      then obtain p q ns' m where ns': "?r p q" "defNode q\<comment>ns'\<rightarrow>m" "defNode q \<notin> set (tl ns')" "q \<in> phiUses m" "m \<in> set (predecessors (defNode p))" "n \<in> set ns'" "set ns' \<subseteq> set ns" "defNode p \<in> set ns"
        by - (drule ns(3)[THEN bspec], auto)
      hence "dominates (defNode q) n" by - (rule defUse_path_dominated, auto)
      moreover from ns' n(2) have n_dom: "dominates n (defNode q)" "dominates n (defNode p)" by - (auto elim!:bspec)
      ultimately have "defNode q = n" by - (rule dominates_antisymm)

      txt {* Therefore, our assumption is wrong and G is either in minimal SSA form or there exist trivial $\phi$ functions. *}
      with ns'(1) n_dom(2) show False by auto
    qed
  qed
end

context CFG_SSA_Transformed
begin
  definition "phiCount = card ((\<lambda>(n,v). (n, var v)) ` dom phis)"

  lemma phiCount: "phiCount = card (dom phis)"
  proof-
    have 1: "v = v'"
      if asm: "phis (n, v) \<noteq> None" "phis (n, v') \<noteq> None" "var v = var v'"
      for n v v'
    proof (rule ccontr)
      from asm have[simp]: "v \<in> allDefs n" "v' \<in> allDefs n" by (auto simp: phiDefs_def allDefs_def)
      from asm have[simp]: "n \<in> set \<alpha>n" by - (auto simp: phis_in_\<alpha>n)
      assume "v \<noteq> v'"
      with asm show False
        by - (rule allDefs_var_disjoint[of n v v', THEN notE], auto)
    qed

    show ?thesis
    unfolding phiCount_def
    apply (rule card_image)
    apply (rule inj_onI)
    by (auto intro!: 1)
  qed

  theorem phi_count_minimal:
    assumes "cytronMinimal" "pruned"
    assumes "CFG_SSA_Transformed \<alpha>n predecessors Entry oldDefs oldUses defs' uses' phis' var'"
    shows "card (dom phis) \<le> card (dom (phis'))"
  proof-
    interpret other: CFG_SSA_Transformed \<alpha>n predecessors Entry oldDefs oldUses defs' uses' phis' var'
      by (rule assms(3))
    {
      fix n v
      assume asm: "phis (n,v) \<noteq> None"
      from asm have[simp]: "v \<in> phiDefs n" "v \<in> allDefs n" by (auto simp: phiDefs_def allDefs_def)
      from asm have[simp]: "defNode v = n" "n \<in> set \<alpha>n" by - (auto simp: phis_in_\<alpha>n)
      from asm have "liveVal v"
        by - (rule \<open>pruned\<close>[unfolded pruned_def, THEN bspec, of n, rule_format]; simp)
      then obtain ns m where ns: "n\<comment>ns\<rightarrow>m" "var v \<in> oldUses m" "\<And>x. x \<in> set (tl ns) \<Longrightarrow> var v \<notin> oldDefs x"
        by (rule liveVal_use_path, simp)
      have "\<exists>v'. phis' (n,v') \<noteq> None \<and> var v = var' v'"
      proof (rule other.convergence_prop'[OF _ ns(1)])
        from asm show "necessaryPhi (var v) n"
          by - (rule \<open>cytronMinimal\<close>[unfolded cytronMinimal_def, THEN bspec, of v, simplified, rule_format],
            auto simp: cytronMinimal_def phi_def, auto intro: allDefs_in_allVars[where n=n])
        with ns(1,2) show "var v \<in> var' ` other.allUses m"
          by (subst(asm) other.oldUses_def, auto simp: image_def allUses_def other.oldUses_def intro!: bexI)
        have "var v \<notin> oldDefs n"
          by (rule simpleDefs_phiDefs_var_disjoint, auto)
        then show "\<And>x. x \<in> set ns \<Longrightarrow> var v \<notin> oldDefs x"
          using ns(1) by (case_tac "x = hd ns", auto dest: ns(3) not_hd_in_tl dest: path2_hd)
      qed auto
    }
    note 1 = this

    have "phiCount \<le> other.phiCount"
    unfolding phiCount_def other.phiCount_def
    apply (rule card_mono)
     apply (rule finite_imageI)
     apply (rule other.phis_finite)
    by (auto simp: dom_def image_def simp del: not_None_eq intro!: 1)

    thus ?thesis by (simp add: phiCount other.phiCount)
  qed
end

end
