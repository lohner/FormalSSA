(*  Title:      Graph_path.thy
    Author:     Sebastian Ullrich
*)

section {* SSA Representation *}

subsection {* Inductive Graph Paths *}

text {* We extend the Graph framework with inductively defined paths.
  We adopt the convention of separating locale definitions into assumption-less base locales. *}

theory Graph_path imports
  "$AFP/Dijkstra_Shortest_Path/GraphSpec"
  FormalSSA_Misc
begin

(*<*)
  declare Digraph_Basic.scc_non_empty' [simp del]
  declare Refine_Misc.strictD_simp [simp del]
(*>*)

type_synonym ('n, 'ed) edge = "('n \<times> 'ed \<times> 'n)"

definition getFrom :: "('n, 'ed) edge \<Rightarrow> 'n" where
  "getFrom \<equiv> fst"
definition getData :: "('n, 'ed) edge \<Rightarrow> 'ed" where
  "getData \<equiv> fst \<circ> snd"
definition getTo :: "('n, 'ed) edge \<Rightarrow> 'n" where
  "getTo \<equiv> snd \<circ> snd"

lemma get_edge_simps [simp]:
  "getFrom (f,d,t) = f"
  "getData (f,d,t) = d"
  "getTo (f,d,t) = t"
  by (simp_all add: getFrom_def getData_def getTo_def)

  text {* Predecessors of a node. *}
  definition pred :: "('v,'w) graph \<Rightarrow> 'v \<Rightarrow> ('v\<times>'w) set"
    where "pred G v \<equiv> {(v',w). (v',w,v)\<in>edges G}"

  lemma pred_finite[simp, intro]: "finite (edges G) \<Longrightarrow> finite (pred G v)"
    unfolding pred_def
    by (rule finite_subset[where B="(\<lambda>(v,w,v'). (v,w))`edges G"]) force+

  lemma pred_empty[simp]: "pred empty v = {}" unfolding empty_def pred_def by auto

  lemma (in valid_graph) pred_subset: "pred G v \<subseteq> V\<times>UNIV"
    unfolding pred_def using E_valid
    by (force)

  type_synonym ('V,'W,'\<sigma>,'G) graph_pred_it =
    "'G \<Rightarrow> 'V \<Rightarrow> ('V\<times>'W,'\<sigma>) set_iterator"

  locale graph_pred_it_defs =
    fixes pred_list_it :: "'G \<Rightarrow> 'V \<Rightarrow> ('V\<times>'W,('V\<times>'W) list) set_iterator"
  begin
    definition "pred_it g v \<equiv> it_to_it (pred_list_it g v)"
  end

  locale graph_pred_it = graph \<alpha> invar + graph_pred_it_defs pred_list_it
    for \<alpha> :: "'G \<Rightarrow> ('V,'W) graph" and invar and
    pred_list_it :: "'G \<Rightarrow> 'V \<Rightarrow> ('V\<times>'W,('V\<times>'W) list) set_iterator" +
    assumes pred_list_it_correct:
      "invar g \<Longrightarrow> set_iterator (pred_list_it g v) (pred (\<alpha> g) v)"
  begin
    lemma pred_it_correct:
      "invar g \<Longrightarrow> set_iterator (pred_it g v) (pred (\<alpha> g) v)"
      unfolding pred_it_def
      apply (rule it_to_it_correct)
      by (rule pred_list_it_correct)

    lemma pi_pred_it[icf_proper_iteratorI]:
      "proper_it (pred_it S v) (pred_it S v)"
      unfolding pred_it_def
      by (intro icf_proper_iteratorI)

    lemma pred_it_proper[proper_it]:
      "proper_it' (\<lambda>S. pred_it S v) (\<lambda>S. pred_it S v)"
      apply (rule proper_it'I)
      by (rule pi_pred_it)
  end

  record ('V,'W,'G) graph_ops = "('V,'W,'G) GraphSpec.graph_ops" +
    gop_pred_list_it :: "'G \<Rightarrow> 'V \<Rightarrow> ('V\<times>'W,('V\<times>'W) list) set_iterator"

  lemma (in graph_pred_it) pred_it_is_iterator[refine_transfer]:
    "invar g \<Longrightarrow> set_iterator (pred_it g v) (pred (\<alpha> g) v)"
    by (rule pred_it_correct)

locale StdGraphDefs = GraphSpec.StdGraphDefs ops
  + graph_pred_it_defs "gop_pred_list_it ops"
  for ops :: "('V,'W,'G,'m) graph_ops_scheme"
begin
  abbreviation pred_list_it  where "pred_list_it \<equiv> gop_pred_list_it ops"
end

locale StdGraph = StdGraphDefs + org:StdGraph +
  graph_pred_it \<alpha> invar pred_list_it

locale graph_path_base_base =
fixes
  \<alpha>n :: "'node list" and
  predecessors :: "'node \<Rightarrow> 'node list"
begin
  definition "inEdges n = map (\<lambda>m. (m,())) (predecessors n)"
end

locale graph_path_base =
  graph_path_base_base \<alpha>n predecessors +
  graph_nodes_it_defs "\<lambda>g. foldri \<alpha>n" +
  graph_pred_it_defs "\<lambda>g n. foldri (inEdges n)"
for
  \<alpha>n :: "'node list" and
  predecessors :: "'node \<Rightarrow> 'node list"
begin
  definition successors :: "'node \<Rightarrow> 'node list" where
    "successors m \<equiv> [n . n \<leftarrow> \<alpha>n, m \<in> set (predecessors n)]"


  declare [[inductive_internals]]
  inductive path :: "'node list \<Rightarrow> bool"
  where
    empty_path[intro]: "\<lbrakk>n \<in> set \<alpha>n\<rbrakk> \<Longrightarrow> path [n]"
    | Cons_path[intro]: "\<lbrakk>path ns; n' \<in> set (predecessors (hd ns))\<rbrakk> \<Longrightarrow> path (n'#ns)"

  definition path2 :: "'node \<Rightarrow> 'node list \<Rightarrow> 'node \<Rightarrow> bool" ("_\<comment>_\<rightarrow>_" [51,0,51] 80) where
    "path2 n ns m \<equiv> path ns \<and> n = hd ns \<and> m = last ns"

  definition "\<alpha>e = {(n,(),m) | n m. n \<in> set (predecessors m)}"

  abbreviation "\<alpha> g \<equiv> \<lparr>nodes = set \<alpha>n, edges = \<alpha>e\<rparr>"
end

locale graph_path =
  graph_path_base \<alpha>n predecessors +
  graph \<alpha> "\<lambda>_::unit. True" +
  ni: graph_nodes_it \<alpha> "\<lambda>_::unit. True" "\<lambda>g. foldri \<alpha>n" +
  pi: graph_pred_it \<alpha> "\<lambda>_::unit. True" "\<lambda>g n. foldri (inEdges n)"
for
  \<alpha>n :: "'node list" and
  predecessors :: "'node \<Rightarrow> 'node list"
begin
  lemma \<alpha>n_correct: "set \<alpha>n \<supseteq> getFrom ` \<alpha>e \<union> getTo ` \<alpha>e"
    using valid by (auto dest: valid_graph.E_validD)

  lemma \<alpha>n_distinct: "distinct \<alpha>n"
    using ni.nodes_list_it_correct
    by (metis foldri_cons_id iterate_to_list_correct iterate_to_list_def)

  lemma distinct_predecessors: "distinct (predecessors n)"
  proof -
    from iterate_to_list_correct [OF pi.pred_list_it_correct [OF assms], of n]
    have "distinct (inEdges n)"
      by (simp add: iterate_to_list_def)
    thus ?thesis unfolding inEdges_def by (auto simp: distinct_map)
  qed

  lemma inEdges_correct':
    shows "set (inEdges n) = pred (\<alpha> g) n"
  proof -
    from iterate_to_list_correct [OF pi.pred_list_it_correct [OF assms], of n]
    show ?thesis
      by (auto intro: rev_image_eqI simp: iterate_to_list_def pred_def)
  qed

  lemma inEdges_correct [simp]:
    "set (inEdges n) = {(f,d). (f,d,n) \<in> \<alpha>e}"
    by (auto simp: inEdges_correct' pred_def)

  lemma in_set_\<alpha>nI1: "x \<in> getFrom ` \<alpha>e \<Longrightarrow> x \<in> set \<alpha>n"
    using \<alpha>n_correct by blast
  lemma in_set_\<alpha>nI2: "x \<in> getTo ` \<alpha>e \<Longrightarrow> x \<in> set \<alpha>n"
    using \<alpha>n_correct by blast

  lemma edge_to_node:
    assumes "e \<in> \<alpha>e"
    obtains "getFrom e \<in> set \<alpha>n" and "getTo e \<in> set \<alpha>n"
  using assms \<alpha>n_correct
    by (cases e) (auto 4 3 intro: rev_image_eqI)

  lemma predecessor_is_node[elim]: "n \<in> set (predecessors n') \<Longrightarrow> n \<in> set \<alpha>n"
    by (rule in_set_\<alpha>nI1, auto simp: getFrom_def \<alpha>e_def)

  lemma successor_is_node[elim]: "n \<in> set (predecessors n') \<Longrightarrow> n' \<in> set \<alpha>n"
   by (rule in_set_\<alpha>nI2, auto simp: getTo_def \<alpha>e_def image_def)

  lemma successors_predecessors[simp]: "n \<in> set \<alpha>n \<Longrightarrow> n \<in> set (successors m) \<longleftrightarrow> m \<in> set (predecessors n)"
    by (auto simp: successors_def)


  lemma path_not_Nil[simp, dest]: "path ns \<Longrightarrow> ns \<noteq> []"
  by (erule path.cases) auto

  lemma path2_not_Nil[simp]: "n\<comment>ns\<rightarrow>m \<Longrightarrow> ns \<noteq> []"
  unfolding path2_def by auto

  lemma path2_not_Nil2[simp]: "\<not> n\<comment>[]\<rightarrow>m"
  unfolding path2_def by auto

  lemma path2_not_Nil3[simp]: "n\<comment>ns\<rightarrow>m \<Longrightarrow> length ns \<ge> 1"
    by (cases ns, auto)

  lemma empty_path2[intro]: "\<lbrakk>n \<in> set \<alpha>n\<rbrakk> \<Longrightarrow> n\<comment>[n]\<rightarrow>n"
  unfolding path2_def by auto

  lemma Cons_path2[intro]: "\<lbrakk>n\<comment>ns\<rightarrow>m; n' \<in> set (predecessors n)\<rbrakk> \<Longrightarrow> n'\<comment>n'#ns\<rightarrow>m"
  unfolding path2_def by auto

  lemma path2_cases:
    assumes "n\<comment>ns\<rightarrow>m"
    obtains (empty_path) "ns = [n]" "m = n"
          | (Cons_path) "hd (tl ns)\<comment>tl ns\<rightarrow>m" "n \<in> set (predecessors (hd (tl ns)))"
  proof-
    from assms have 1: "path ns" "hd ns = n" "last ns = m" by (auto simp: path2_def)
    from this(1) show thesis
    proof cases
      case (empty_path n)
      with 1 show thesis by - (rule that(1), auto)
    next
      case (Cons_path ns n')
      with 1 show thesis by - (rule that(2), auto simp: path2_def)
    qed
  qed

  lemma path2_induct[consumes 1, case_names empty_path Cons_path]:
    assumes "n\<comment>ns\<rightarrow>m"
    assumes empty: "P m [m] m"
    assumes Cons: "\<And>ns n' n. n\<comment>ns\<rightarrow>m \<Longrightarrow> P n ns m \<Longrightarrow> n' \<in> set (predecessors n) \<Longrightarrow> P n' (n' # ns) m"
    shows "P n ns m"
  using assms(1)
  unfolding path2_def
  apply-
  proof (erule conjE, induction arbitrary: n rule:path.induct)
    case empty_path
    with empty show ?case by simp
  next
    case (Cons_path ns n' n'')
    hence[simp]: "n'' = n'" by simp
    from Cons_path Cons show ?case unfolding path2_def by auto
  qed

  lemma path_in_\<alpha>n[intro]: "\<lbrakk>path ns; n \<in> set ns\<rbrakk> \<Longrightarrow> n \<in> set \<alpha>n"
  by (induct ns arbitrary: n rule:path.induct) auto

  lemma path2_in_\<alpha>n[elim]: "\<lbrakk>n\<comment>ns\<rightarrow>m; l \<in> set ns\<rbrakk> \<Longrightarrow> l \<in> set \<alpha>n"
  unfolding path2_def by auto

  lemma path2_hd_in_\<alpha>n[elim]: "n\<comment>ns\<rightarrow>m \<Longrightarrow> n \<in> set \<alpha>n"
  unfolding path2_def by auto

  lemma path2_tl_in_\<alpha>n[elim]: "n\<comment>ns\<rightarrow>m \<Longrightarrow> m \<in> set \<alpha>n"
  unfolding path2_def by auto

  lemma path2_forget_hd[simp]: "n\<comment>ns\<rightarrow>m \<Longrightarrow> hd ns\<comment>ns\<rightarrow>m"
  unfolding path2_def by simp

  lemma path2_forget_last[simp]: "n\<comment>ns\<rightarrow>m \<Longrightarrow> n\<comment>ns\<rightarrow>last ns"
  unfolding path2_def by simp

  lemma path_hd[dest]: "path (n#ns) \<Longrightarrow> path [n]"
  by (rule empty_path, auto elim:path.cases)

  lemma path_by_tail[intro]: "\<lbrakk>path (n#n'#ns); path (n'#ns) \<Longrightarrow> path (n'#ms)\<rbrakk> \<Longrightarrow> path (n#n'#ms)"
  by (rule path.cases) auto

  lemma \<alpha>n_in_\<alpha>nE [elim]:
    assumes "(n,e,m) \<in> \<alpha>e"
    obtains "n \<in> set \<alpha>n" and "m \<in> set \<alpha>n"
    using assms
    by (auto elim: edge_to_node)

  lemma path_split:
    assumes "path (ns@m#ns')"
    shows "path (ns@[m])" "path(m#ns')"
  proof-
    from assms show "path (ns@[m])"
    proof (induct ns)
      case (Cons n ns)
      thus ?case by (cases ns) auto
    qed auto
    from assms show "path (m#ns')"
    proof (induct ns)
      case (Cons n ns)
      thus ?case by (auto elim:path.cases)
    qed auto
  qed

  lemma path2_split:
    assumes "n\<comment>ns@n'#ns'\<rightarrow>m"
    shows "n\<comment>ns@[n']\<rightarrow>n'" "n'\<comment>n'#ns'\<rightarrow>m"
  using assms unfolding path2_def by (auto intro:path_split iff:hd_append)

  lemma elem_set_implies_elem_tl_app_cons[simp]: "x \<in> set xs \<Longrightarrow> x \<in> set (tl (ys@y#xs))"
    by (induction ys arbitrary: y; auto)

  lemma path2_split_ex:
    assumes "n\<comment>ns\<rightarrow>m" "x \<in> set ns"
    obtains ns\<^sub>1 ns\<^sub>2 where "n\<comment>ns\<^sub>1\<rightarrow>x" "x\<comment>ns\<^sub>2\<rightarrow>m" "ns = ns\<^sub>1@tl ns\<^sub>2" "ns = butlast ns\<^sub>1@ns\<^sub>2"
  proof-
    from assms(2) obtain ns\<^sub>1 ns\<^sub>2 where "ns = ns\<^sub>1@x#ns\<^sub>2" by atomize_elim (rule split_list)
    with assms[simplified this] show thesis
      by - (rule that, auto dest:path2_split(1) path2_split(2) intro: suffixeqI)
  qed

  lemma path2_split_ex':
    assumes "n\<comment>ns\<rightarrow>m" "x \<in> set ns"
    obtains ns\<^sub>1 ns\<^sub>2 where "n\<comment>ns\<^sub>1\<rightarrow>x" "x\<comment>ns\<^sub>2\<rightarrow>m" "ns = butlast ns\<^sub>1@ns\<^sub>2"
  using assms by (rule path2_split_ex)

  lemma path_snoc:
    assumes "path (ns@[n])" "n \<in> set (predecessors m)"
    shows "path (ns@[n,m])"
  using assms(1) proof (induction ns)
    case Nil
    hence 1: "n \<in> set \<alpha>n" by auto
    with assms(2) have "m \<in> set \<alpha>n" by auto
    with 1 have "path [m]" by auto
    with assms(2) show ?case by auto
  next
    case (Cons l ns)
    hence 1: "path (ns @ [n]) \<and> l \<in> set (predecessors (hd (ns@[n])))" by -(cases "(l # ns) @ [n]" rule:path.cases, auto)
    hence "path (ns @ [n,m])" by (auto intro:Cons.IH)
    with 1 have "path (l # ns @ [n,m])" by -(rule Cons_path, assumption, cases ns, auto)
    thus ?case by simp
  qed

  lemma path2_snoc[elim]:
    assumes "n\<comment>ns\<rightarrow>m" "m \<in> set (predecessors m')"
    shows "n\<comment>ns@[m']\<rightarrow>m'"
  proof-
    from assms(1) have 1: "ns \<noteq> []" by auto

    have "path ((butlast ns) @ [last ns, m'])"
    using assms unfolding path2_def by -(rule path_snoc, auto)
    hence "path ((butlast ns @ [last ns]) @ [m'])" by simp
    with 1 have "path (ns @ [m'])" by simp
    thus ?thesis
    using assms unfolding path2_def by auto
  qed

  lemma path_unsnoc:
    assumes "path ns" "length ns \<ge> 2"
    obtains "path (butlast ns) \<and> last (butlast ns) \<in> set (predecessors (last ns))"
  using assms
  proof (atomize_elim, induction ns)
    case (Cons_path ns n)
    show ?case
    proof (cases "2 \<le> length ns")
      case True
        hence [simp]: "hd (butlast ns) = hd ns" by (cases ns, auto)
        have 0: "n#butlast ns = butlast (n#ns)" using True by auto
        have 1: "n \<in> set (predecessors (hd (butlast ns)))" using Cons_path by simp
        from True have "path (butlast ns)" using Cons_path by auto
        hence "path (n#butlast ns)" using 1 by auto
        hence "path (butlast (n#ns))" using 0 by simp
      moreover
        from Cons_path True have "last (butlast ns) \<in> set (predecessors (last ns))" by simp
        hence "last (butlast (n # ns)) \<in> set (predecessors (last (n # ns)))"
          using True by (cases ns, auto)
      ultimately show ?thesis by auto
    next
      case False
      thus ?thesis
      proof (cases ns)
        case Nil
        thus ?thesis using Cons_path by -(rule ccontr, auto elim:path.cases)
      next
        case (Cons n' ns')
        hence [simp]: "ns = [n']" using False by (cases ns', auto)
        have "path [n,n']" using Cons_path by auto
        thus ?thesis using Cons_path by auto
      qed
    qed
  qed auto

  lemma path2_unsnoc:
    assumes "n\<comment>ns\<rightarrow>m" "length ns \<ge> 2"
    obtains "n\<comment>butlast ns\<rightarrow>last (butlast ns)" "last (butlast ns) \<in> set (predecessors m)"
  using assms unfolding path2_def by (metis append_butlast_last_id hd_append2 path_not_Nil path_unsnoc)

  lemma path2_rev_induct[consumes 1, case_names empty snoc]:
    assumes "n\<comment>ns\<rightarrow>m"
    assumes empty: "n \<in> set \<alpha>n \<Longrightarrow> P n [n] n"
    assumes snoc: "\<And>ns m' m. n\<comment>ns\<rightarrow>m' \<Longrightarrow> P n ns m' \<Longrightarrow> m' \<in> set (predecessors m) \<Longrightarrow> P n (ns@[m]) m"
    shows "P n ns m"
  using assms(1) proof (induction arbitrary:m rule:length_induct)
    case (1 ns)
    show ?case
    proof (cases "length ns \<ge> 2")
      case False
      thus ?thesis
      proof (cases ns)
        case Nil
        thus ?thesis using 1(2) by auto
      next
        case (Cons n' ns')
        with False have "ns' = []" by (cases ns', auto)
        with Cons 1(2) have "n' = n" "m = n" unfolding path2_def by auto
        with Cons `ns' = []` 1(2) show ?thesis by (auto intro:empty)
      qed
    next
      case True
      let ?ns' = "butlast ns"
      let ?m' = "last ?ns'"
      from 1(2) have m: "m = last ns" unfolding path2_def by auto
      from True 1(2) obtain ns': "n\<comment>?ns'\<rightarrow>?m'" "?m' \<in> set (predecessors m)" by -(rule path2_unsnoc)
      with True "1.IH" have "P n ?ns' ?m'" by auto
      with ns' have "P n (?ns'@[m]) m" by (auto intro!: snoc)
      with m 1(2) show ?thesis by auto
    qed
  qed

  lemma path2_hd[elim, dest?]: "n\<comment>ns\<rightarrow>m \<Longrightarrow> n = hd ns"
  unfolding path2_def by simp

  lemma path2_hd_in_ns[elim]: "n\<comment>ns\<rightarrow>m \<Longrightarrow> n \<in> set ns"
  unfolding path2_def by auto

  lemma path2_last[elim, dest?]: "n\<comment>ns\<rightarrow>m \<Longrightarrow> m = last ns"
  unfolding path2_def by simp

  lemma path2_last_in_ns[elim]: "n\<comment>ns\<rightarrow>m \<Longrightarrow> m \<in> set ns"
  unfolding path2_def by auto

  lemma path_app[elim]:
    assumes "path ns" "path ms" "last ns = hd ms"
    shows "path (ns@tl ms)"
  using assms by (induction ns rule:path.induct) auto

  lemma path2_app[elim]:
    assumes "n\<comment>ns\<rightarrow>m" "m\<comment>ms\<rightarrow>l"
    shows "n\<comment>ns@tl ms\<rightarrow>l"
  proof-
    have "last (ns @ tl ms) = last ms" using assms
    unfolding path2_def
    proof (cases "tl ms")
      case Nil
      hence "ms = [m]" using assms(2) unfolding path2_def by (cases ms, auto)
      thus ?thesis using assms(1) unfolding path2_def by auto
    next
      case (Cons m' ms')
      from this[symmetric] have "ms = hd ms#m'#ms'" using assms(2) by auto
      thus ?thesis using assms unfolding path2_def by auto
    qed
    with assms show ?thesis
      unfolding path2_def by auto
  qed

  lemma butlast_tl:
    assumes "last xs = hd ys" "xs \<noteq> []" "ys \<noteq> []"
    shows "butlast xs@ys = xs@tl ys"
    by (metis append.simps(1) append.simps(2) append_assoc append_butlast_last_id assms(1) assms(2) assms(3) list.collapse)

  lemma path2_app'[elim]:
    assumes "n\<comment>ns\<rightarrow>m" "m\<comment>ms\<rightarrow>l"
    shows "n\<comment>butlast ns@ms\<rightarrow>l"
  proof-
    have "butlast ns@ms = ns@tl ms" using assms by - (rule butlast_tl, auto dest:path2_hd path2_last)
    moreover from assms have "n\<comment>ns@tl ms\<rightarrow>l" by (rule path2_app)
    ultimately show ?thesis by simp
  qed

  lemma path2_nontrivial[elim]:
    assumes "n\<comment>ns\<rightarrow>m" "n \<noteq> m"
    shows "length ns \<ge> 2"
  using assms
    by (metis Suc_1 le_antisym length_1_last_hd not_less_eq_eq path2_hd path2_last path2_not_Nil3)

  lemma simple_path2_aux:
    assumes "n\<comment>ns\<rightarrow>m"
    obtains ns' where "n\<comment>ns'\<rightarrow>m" "distinct ns'" "set ns' \<subseteq> set ns" "length ns' \<le> length ns"
  apply atomize_elim
  using assms proof (induction rule:path2_induct)
    case empty_path
    with assms show ?case by - (rule exI[of _ "[m]"], auto)
  next
    case (Cons_path ns n n')
    then obtain ns' where ns': "n'\<comment>ns'\<rightarrow>m" "distinct ns'" "set ns' \<subseteq> set ns" "length ns' \<le> length ns" by auto
    show ?case
    proof (cases "n \<in> set ns'")
      case False
      with ns' Cons_path(2) show ?thesis by -(rule exI[where x="n#ns'"], auto)
    next
      case True
      with ns' obtain ns'\<^sub>1 ns'\<^sub>2 where split: "ns' = ns'\<^sub>1@n#ns'\<^sub>2" "n \<notin> set ns'\<^sub>2" by -(atomize_elim, rule split_list_last)
      with ns' have "n\<comment>n#ns'\<^sub>2\<rightarrow>m" by -(rule path2_split, simp)
      with split ns' show ?thesis by -(rule exI[where x="n#ns'\<^sub>2"], auto)
    qed
  qed

  lemma simple_path2:
    assumes "n\<comment>ns\<rightarrow>m"
    obtains ns' where "n\<comment>ns'\<rightarrow>m" "distinct ns'" "set ns' \<subseteq> set ns" "length ns' \<le>  length ns" "n \<notin> set (tl ns')" "m \<notin> set (butlast ns')"
  using assms
  apply (rule simple_path2_aux)
  by (metis append_butlast_last_id distinct.simps(2) distinct1_rotate hd_Cons_tl path2_hd path2_last path2_not_Nil rotate1.simps(2))

  lemma simple_path2_unsnoc:
    assumes "n\<comment>ns\<rightarrow>m" "n \<noteq> m"
    obtains ns' where "n\<comment>ns'\<rightarrow>last ns'" "last ns' \<in> set (predecessors m)" "distinct ns'" "set ns' \<subseteq> set ns" "m \<notin> set ns'"
  proof-
    obtain ns' where 1: "n\<comment>ns'\<rightarrow>m" "distinct ns'" "set ns' \<subseteq> set ns" "m \<notin> set (butlast ns')" by (rule simple_path2[OF assms(1)])
    with assms(2) obtain 2: "n\<comment>butlast ns'\<rightarrow>last (butlast ns')" "last (butlast ns') \<in> set (predecessors m)" by - (rule path2_unsnoc, auto)
    show thesis
    proof (rule that[of "butlast ns'"])
      from 1(3) show "set (butlast ns') \<subseteq> set ns" by (metis in_set_butlastD subsetI subset_trans)
    qed (auto simp:1 2 distinct_butlast)
  qed

  lemma path2_split_first_last:
    assumes "n\<comment>ns\<rightarrow>m" "x \<in> set ns"
    obtains ns\<^sub>1 ns\<^sub>3 ns\<^sub>2 where "ns = ns\<^sub>1@ns\<^sub>3@ns\<^sub>2" "prefixeq (ns\<^sub>1@[x]) ns" "suffixeq (x#ns\<^sub>2) ns"
        and "n\<comment>ns\<^sub>1@[x]\<rightarrow>x"  "x \<notin> set ns\<^sub>1"
        and "x\<comment>ns\<^sub>3\<rightarrow>x"
        and "x\<comment>x#ns\<^sub>2\<rightarrow>m" "x \<notin> set ns\<^sub>2"
  proof-
    from assms(2) obtain ns\<^sub>1 ns' where 1: "ns = ns\<^sub>1@x#ns'" "x \<notin> set ns\<^sub>1" by (atomize_elim, rule split_list_first)
    from assms(1)[unfolded 1(1)] have 2: "n\<comment>ns\<^sub>1@[x]\<rightarrow>x" "x\<comment>x#ns'\<rightarrow>m" by - (erule path2_split, erule path2_split)
    obtain ns\<^sub>3 ns\<^sub>2 where 3: "x#ns' = ns\<^sub>3@x#ns\<^sub>2" "x \<notin> set ns\<^sub>2" by (atomize_elim, rule split_list_last, simp)
    from 2(2)[unfolded 3(1)] have 4: "x\<comment>ns\<^sub>3@[x]\<rightarrow>x" "x\<comment>x#ns\<^sub>2\<rightarrow>m" by - (erule path2_split, erule path2_split)
    show thesis
    proof (rule that[OF _ _ _ 2(1) 1(2) 4 3(2)])
      show "ns = ns\<^sub>1 @ (ns\<^sub>3 @ [x]) @ ns\<^sub>2" using 1(1) 3(1) by simp
      show "prefixeq (ns\<^sub>1@[x]) ns" using 1 by auto
      show "suffixeq (x#ns\<^sub>2) ns" using 1 3 by (metis suffixeq_def suffixeq_trans)
    qed
  qed

  lemma path2_simple_loop:
    assumes "n\<comment>ns\<rightarrow>n" "n' \<in> set ns"
    obtains ns' where "n\<comment>ns'\<rightarrow>n" "n' \<in> set ns'" "n \<notin> set (tl (butlast ns'))" "set ns' \<subseteq> set ns"
  using assms proof (induction "length ns" arbitrary: ns rule: nat_less_induct)
    case 1
    let ?ns' = "tl (butlast ns)"
    show ?case
    proof (cases "n \<in> set ?ns'")
      case False
      with "1.prems"(2,3) show ?thesis by - (rule "1.prems"(1), auto)
    next
      case True
      hence 2: "length ns > 1" by (cases ns, auto)
      with "1.prems"(2) obtain m where m: "n\<comment>butlast ns\<rightarrow>m" "m \<in> set (predecessors n)" by - (rule path2_unsnoc, auto)
      with True obtain m' where m': "m'\<comment>?ns'\<rightarrow>m" "n \<in> set (predecessors m')" by - (erule path2_cases, auto)
      with True obtain ns\<^sub>1 ns\<^sub>2 where split: "m'\<comment>ns\<^sub>1\<rightarrow>n" "n\<comment>ns\<^sub>2\<rightarrow>m" "?ns' = ns\<^sub>1@tl ns\<^sub>2" "?ns' = butlast ns\<^sub>1@ns\<^sub>2"
        by - (rule path2_split_ex)
      have "ns = butlast ns@[n]" using 2 "1.prems"(2) by (auto simp: path2_def)
      moreover have "butlast ns = n#tl (butlast ns)" using 2 m(1) by (auto simp: path2_def)
      ultimately have split': "ns = n#ns\<^sub>1@tl ns\<^sub>2@[n]" "ns = n#butlast ns\<^sub>1@ns\<^sub>2@[n]" using split(3,4) by auto
      show ?thesis
      proof (cases "n' \<in> set (n#ns\<^sub>1)")
        case True
        show ?thesis
        proof (rule "1.hyps"[rule_format, of _ "n#ns\<^sub>1"])
          show "length (n#ns\<^sub>1) < length ns" using split'(1) by auto
          show "n' \<in> set (n#ns\<^sub>1)" by (rule True)
        qed (auto intro: split(1) m'(2) intro!: "1.prems"(1) simp: split'(1))
      next
        case False
        from False split'(1) "1.prems"(3) have 5: "n' \<in> set (ns\<^sub>2@[n])" by auto
        show ?thesis
        proof (rule "1.hyps"[rule_format, of _ "ns\<^sub>2@[n]"])
          show "length (ns\<^sub>2@[n]) < length ns" using split'(2) by auto
          show "n' \<in> set (ns\<^sub>2@[n])" by (rule 5)
          show "n\<comment>ns\<^sub>2@[n]\<rightarrow>n" using split(2) m(2) by (rule path2_snoc)
        qed (auto intro!: "1.prems"(1) simp: split'(2))
      qed
    qed
  qed

  lemma path2_split_first_prop:
    assumes "n\<comment>ns\<rightarrow>m" "\<exists>x\<in>set ns. P x"
    obtains m' ns' where "n\<comment>ns'\<rightarrow>m'" "P m'" "\<forall>x \<in> set (butlast ns'). \<not>P x" "prefixeq ns' ns"
  proof-
    obtain ns'' n' ns' where 1: "ns = ns''@n'#ns'" "P n'" "\<forall>x \<in> set ns''. \<not>P x" by - (rule split_list_first_propE[OF assms(2)])
    with assms(1) have "n\<comment>ns''@[n']\<rightarrow>n'" by - (rule path2_split(1), auto)
    with 1 show thesis by - (rule that, auto)
  qed

  lemma path2_split_last_prop:
    assumes "n\<comment>ns\<rightarrow>m" "\<exists>x\<in>set ns. P x"
    obtains n' ns' where "n'\<comment>ns'\<rightarrow>m" "P n'" "\<forall>x \<in> set (tl ns'). \<not>P x" "suffixeq ns' ns"
  proof-
    obtain ns'' n' ns' where 1: "ns = ns''@n'#ns'" "P n'" "\<forall>x \<in> set ns'. \<not>P x" by - (rule split_list_last_propE[OF assms(2)])
    with assms(1) have "n'\<comment>n'#ns'\<rightarrow>m" by - (rule path2_split(2), auto)
    with 1 show thesis by - (rule that, auto simp:suffixeq_def)
  qed

  lemma path2_prefix[elim]:
    assumes 1: "n\<comment>ns\<rightarrow>m"
    assumes 2: "prefixeq (ns'@[m']) ns"
    shows "n\<comment>ns'@[m']\<rightarrow>m'"
  using assms by -(erule prefixeqE, rule path2_split, simp)

  lemma path2_prefix_ex:
    assumes "n\<comment>ns\<rightarrow>m" "m' \<in> set ns"
    obtains ns' where "n\<comment>ns'\<rightarrow>m'" "prefixeq ns' ns" "m' \<notin> set (butlast ns')"
  proof-
    from assms(2) obtain ns' where "prefixeq (ns'@[m']) ns" "m' \<notin> set ns'" by (rule prefix_split_first)
    with assms(1) show thesis by - (rule that, auto)
  qed

  lemma path2_strict_prefix_ex:
    assumes "n\<comment>ns\<rightarrow>m" "m' \<in> set (butlast ns)"
    obtains ns' where "n\<comment>ns'\<rightarrow>m'" "prefix ns' ns" "m' \<notin> set (butlast ns')"
  proof-
    from assms(2) obtain ns' where ns': "prefixeq (ns'@[m']) (butlast ns)" "m' \<notin> set ns'" by (rule prefix_split_first)
    hence "prefix (ns'@[m']) ns" using assms by - (rule strict_prefix_butlast, auto)
    with assms(1) ns'(2) show thesis by - (rule that, auto)
  qed

  lemma path2_nontriv[elim]: "\<lbrakk>n\<comment>ns\<rightarrow>m; n \<noteq> m\<rbrakk> \<Longrightarrow> length ns > 1"
    by (metis hd_Cons_tl last_appendR last_snoc length_greater_0_conv length_tl path2_def path_not_Nil zero_less_diff)

  declare path_not_Nil [simp del]
  declare path2_not_Nil [simp del]
  declare path2_not_Nil3 [simp del]
end

subsection {* Domination *}

text {* We fix an entry node per graph and use it to define node domination. *}

locale graph_Entry_base = graph_path_base \<alpha>n predecessors
for
  \<alpha>n :: "'node list" and
  predecessors :: "'node \<Rightarrow> 'node list"
+
fixes Entry :: "'node"
begin
  definition dominates :: "'node \<Rightarrow> 'node \<Rightarrow> bool" where
    "dominates n m \<equiv> m \<in> set \<alpha>n \<and> (\<forall>ns. Entry\<comment>ns\<rightarrow>m \<longrightarrow> n \<in> set ns)"

  abbreviation "strict_dom n m \<equiv> n \<noteq> m \<and> dominates n m"
end

locale graph_Entry = graph_Entry_base \<alpha>n predecessors Entry
  + graph_path \<alpha>n predecessors
for
  \<alpha>n :: "'node list" and
  predecessors :: "'node \<Rightarrow> 'node list" and
  Entry :: "'node"
+
assumes Entry_in_graph[simp]: "Entry \<in> set \<alpha>n"
assumes Entry_unreachable[simp]: "predecessors (Entry) = []"
assumes Entry_reaches[intro]:
  "\<lbrakk>n \<in> set \<alpha>n\<rbrakk> \<Longrightarrow> \<exists>ns. Entry\<comment>ns\<rightarrow>n"
begin
  lemma Entry_dominates[simp,intro]: "\<lbrakk>n \<in> set \<alpha>n\<rbrakk> \<Longrightarrow> dominates (Entry) n"
  unfolding dominates_def by auto

  lemma Entry_iff_unreachable[simp]:
    assumes "n \<in> set \<alpha>n"
    shows "predecessors n = [] \<longleftrightarrow> n = Entry"
  proof (rule, rule ccontr)
    assume "predecessors n = []" "n \<noteq> Entry"
    with Entry_reaches[OF assms(1)] show False by (auto elim:simple_path2_unsnoc)
  qed (auto simp:assms Entry_unreachable)

  lemma Entry_loop:
    assumes "Entry\<comment>ns\<rightarrow>Entry"
    shows "ns=[Entry]"
  proof (cases "length ns \<ge> 2")
    case True
    with assms have "last (butlast ns) \<in> set (predecessors (Entry))" by - (rule path2_unsnoc)
    with Entry_unreachable have False by simp
    thus ?thesis ..
  next
    case False
    with assms show ?thesis
      by (metis Suc_leI hd_Cons_tl impossible_Cons le_less length_greater_0_conv numeral_2_eq_2 path2_hd path2_not_Nil)
  qed

  lemma simple_Entry_path:
    assumes "n \<in> set \<alpha>n"
    obtains ns where "Entry\<comment>ns\<rightarrow>n" and "n \<notin> set (butlast ns)"
  proof-
    from assms obtain ns where p: "Entry\<comment>ns\<rightarrow>n" by -(atomize_elim, rule Entry_reaches)
    with p obtain ns' where "Entry\<comment>ns'\<rightarrow>n" "n \<notin> set (butlast ns')" by -(rule path2_split_first_last, auto)
    thus ?thesis by (rule that)
  qed

  lemma dominatesI:
    "\<lbrakk>m \<in> set \<alpha>n; \<And>ns. \<lbrakk>Entry\<comment>ns\<rightarrow>m\<rbrakk> \<Longrightarrow> n \<in> set ns\<rbrakk> \<Longrightarrow> dominates n m"
  unfolding dominates_def by simp

  lemma dominatesE:
    assumes "dominates n m"
    obtains "m \<in> set \<alpha>n" and "\<And>ns. Entry\<comment>ns\<rightarrow>m \<Longrightarrow> n \<in> set ns"
    using assms unfolding dominates_def by auto

  lemma dominated_in_\<alpha>n[elim!]: "dominates n m \<Longrightarrow> m \<in> set \<alpha>n" by (rule dominatesE)

  lemma dominator_in_\<alpha>n[elim!]:
    assumes "dominates n m"
    shows "n \<in> set \<alpha>n"
  proof-
    from assms obtain ns where "Entry\<comment>ns\<rightarrow>m" by atomize_elim (rule Entry_reaches, auto)
    with assms show ?thesis by (auto elim!:dominatesE)
  qed

  lemma strict_domE[elim]:
    assumes "strict_dom n m"
    obtains "m \<in> set \<alpha>n" and "\<And>ns. Entry\<comment>ns\<rightarrow>m \<Longrightarrow> n \<in> set (butlast ns)"
  using assms by (metis dominates_def path2_def path_not_Nil rotate1.simps(2) set_ConsD set_rotate1 snoc_eq_iff_butlast)

  lemma dominates_refl[intro!]: "\<lbrakk>n \<in> set \<alpha>n\<rbrakk> \<Longrightarrow> dominates n n"
  by (rule dominatesI, auto)

  lemma dominates_trans[trans]:
    assumes part1: "dominates n n'"
    assumes part2: "dominates n' n''"
    shows   "dominates n n''"
  proof (rule dominatesI)
    from part2 show "n'' \<in> set \<alpha>n" by auto

    fix ns :: "'node list"
    assume p: "Entry\<comment>ns\<rightarrow>n''"
    with part2 have "n' \<in> set ns" by - (erule dominatesE, auto)
    then obtain as where prefix: "prefixeq (as@[n']) ns" by (auto intro:prefix_split_first)
    with p have "Entry\<comment>(as@[n'])\<rightarrow>n'" by auto
    with part1 have "n \<in> set (as@[n'])" unfolding dominates_def by auto
    with prefix show "n \<in> set ns" by auto
  qed

  lemma dominates_antisymm:
    assumes dom1: "dominates n n'"
    assumes dom2: "dominates n' n"
    shows "n = n'"
  proof (rule ccontr)
    assume "n \<noteq> n'"
    from dom2 have "n \<in> set \<alpha>n" by auto
    then obtain ns where p: "Entry\<comment>ns\<rightarrow>n" and "n \<notin> set (butlast ns)"
      by (rule simple_Entry_path)
    with dom2 have "n' \<in> set ns" by - (erule dominatesE, auto)
    then obtain as where prefix: "prefixeq (as@[n']) ns" by (auto intro:prefix_split_first)
    with p have "Entry\<comment>as@[n']\<rightarrow>n'" by (rule path2_prefix)
    with dom1 have "n \<in> set (as@[n'])" unfolding dominates_def by auto
    with `n \<noteq> n'` have "n \<in> set as" by auto
    with `prefixeq (as@[n']) ns` have "n \<in> set (butlast ns)" by -(erule prefixeqE, auto iff:butlast_append)
    with `n \<notin> set (butlast ns)` show False..
  qed

  lemma dominates_unsnoc:
    assumes "dominates n m" "m' \<in> set (predecessors m)" "n \<noteq> m"
    shows "dominates n m'"
  proof (rule dominatesI)
    show "m' \<in> set \<alpha>n" using assms by auto
  next
    fix ns
    assume "Entry\<comment>ns\<rightarrow>m'"
    with assms(2) have "Entry\<comment>ns@[m]\<rightarrow>m" by auto
    with assms(1,3) show "n \<in> set ns" by (auto elim!:dominatesE)
  qed

  lemma dominates_unsnoc':
    assumes "dominates n m" "m'\<comment>ms\<rightarrow>m" "\<forall>x \<in> set (tl ms). x \<noteq> n"
    shows "dominates n m'"
  using assms(2,3) proof (induction rule:path2_induct)
    case empty_path
    show ?case by (rule assms(1))
  next
    case (Cons_path ms m'' m')
    from Cons_path(4) have "dominates n m'"
      by (simp add: Cons_path.IH in_set_tlD)
    moreover from Cons_path(1) have "m' \<in> set ms" by auto
    hence "m' \<noteq> n" using Cons_path(4) by simp
    ultimately show ?case using Cons_path(2) by - (rule dominates_unsnoc, auto)
  qed

  lemma dominates_path:
    assumes "dominates n m"
    obtains ns where "n\<comment>ns\<rightarrow>m"
  proof atomize_elim
    from assms obtain ns where ns: "Entry\<comment>ns\<rightarrow>m" by atomize_elim (rule Entry_reaches, auto)
    with assms have "n \<in> set ns" by - (erule dominatesE)
    with ns show "\<exists>ns. n\<comment>ns\<rightarrow>m" by - (rule path2_split_ex, auto)
  qed

  lemma dominates_antitrans:
    assumes "dominates n\<^sub>1 m" "dominates n\<^sub>2 m"
    obtains (1) "dominates n\<^sub>1 n\<^sub>2"
          | (2) "dominates n\<^sub>2 n\<^sub>1"
  proof (cases "dominates n\<^sub>1 n\<^sub>2")
    case False
    show thesis
    proof (rule 2, rule dominatesI)
      show "n\<^sub>1 \<in> set \<alpha>n" using assms(1) by (rule dominator_in_\<alpha>n)
    next
      fix ns
      assume asm: "Entry\<comment>ns\<rightarrow>n\<^sub>1"
      from assms(1) obtain ns\<^sub>2 where "n\<^sub>1\<comment>ns\<^sub>2\<rightarrow>m" by (rule dominates_path, simp)
      then obtain ns\<^sub>2' where ns\<^sub>2': "n\<^sub>1\<comment>ns\<^sub>2'\<rightarrow>m" "n\<^sub>1 \<notin> set (tl ns\<^sub>2')" "set ns\<^sub>2' \<subseteq> set ns\<^sub>2" by (rule simple_path2)
      with asm have "Entry\<comment>ns@tl ns\<^sub>2'\<rightarrow>m" by auto
      with assms(2) have "n\<^sub>2 \<in> set (ns@tl ns\<^sub>2')" by - (erule dominatesE)
      moreover have "n\<^sub>2 \<notin> set (tl ns\<^sub>2')"
      proof
        assume "n\<^sub>2 \<in> set (tl ns\<^sub>2')"
        with ns\<^sub>2'(1,2) obtain ns\<^sub>3 where ns\<^sub>3: "n\<^sub>2\<comment>ns\<^sub>3\<rightarrow>m" "n\<^sub>1 \<notin> set (tl ns\<^sub>3)"
          by - (erule path2_split_ex, auto simp: path2_not_Nil)
        have "dominates n\<^sub>1 n\<^sub>2"
        proof (rule dominatesI)
          show "n\<^sub>2 \<in> set \<alpha>n" using assms(2) by (rule dominator_in_\<alpha>n)
        next
          fix ns'
          assume ns': "Entry\<comment>ns'\<rightarrow>n\<^sub>2"
          with ns\<^sub>3(1) have "Entry\<comment>ns'@tl ns\<^sub>3\<rightarrow>m" by auto
          with assms(1) have "n\<^sub>1 \<in> set (ns'@tl ns\<^sub>3)" by - (erule dominatesE)
          with ns\<^sub>3(2) show "n\<^sub>1 \<in> set ns'" by simp
        qed
        with False show False ..
      qed
      ultimately show "n\<^sub>2 \<in> set ns" by simp
    qed
  qed

  lemma dominates_extend:
    assumes "dominates n m"
    assumes "m'\<comment>ms\<rightarrow>m" "n \<notin> set (tl ms)"
    shows "dominates n m'"
  proof (rule dominatesI)
    show "m' \<in> set \<alpha>n" using assms(2) by auto
  next
    fix ms'
    assume "Entry\<comment>ms'\<rightarrow>m'"
    with assms(2) have "Entry\<comment>ms'@tl ms\<rightarrow>m" by auto
    with assms(1) have "n \<in> set (ms'@tl ms)" by - (erule dominatesE)
    with assms(3) show "n \<in> set ms'" by auto
  qed

  definition dominators :: "'node \<Rightarrow> 'node set" where
    "dominators n \<equiv> {m \<in> set \<alpha>n. dominates m n}"

  definition "isIdom n m \<longleftrightarrow> strict_dom m n \<and> (\<forall>m' \<in> set \<alpha>n. strict_dom m' n \<longrightarrow> dominates m' m)"
  definition idom :: "'node \<Rightarrow> 'node" where
    "idom n \<equiv> THE m. isIdom n m"

  lemma idom_ex:
    assumes[simp]: "n \<in> set \<alpha>n" "n \<noteq> Entry"
    shows "\<exists>!m. isIdom n m"
  proof (rule ex_ex1I)
    let ?A = "\<lambda>m. {m' \<in> set \<alpha>n. strict_dom m' n \<and> strict_dom m m'}"

    have 1: "\<And>A m. finite A \<Longrightarrow> A = ?A m \<Longrightarrow> strict_dom m n \<Longrightarrow> \<exists>m'. isIdom n m'"
    proof-
      fix A m
      show "finite A \<Longrightarrow> A = ?A m \<Longrightarrow> strict_dom m n \<Longrightarrow> \<exists>m'. isIdom n m'"
      proof (induction arbitrary:m rule:finite_psubset_induct)
        case (psubset A m)
        show ?case
        proof (cases "A = {}")
          case True
          { fix m'
            assume asm: "strict_dom m' n" and [simp]: "m' \<in> set \<alpha>n"
            with True psubset.prems(1) have "\<not>(strict_dom m m')" by auto
            hence "dominates m' m" using asm psubset.prems(2)
              by - (rule dominates_antitrans[of m' n m]; auto)
          }
          thus ?thesis using psubset.prems(2) by - (rule exI[of _ m], auto simp:isIdom_def)
        next
          case False
          then obtain m' where "m' \<in> A" by auto
          with psubset.prems(1) have m': "m' \<in> set \<alpha>n" "strict_dom m' n" "strict_dom m m'" by auto
          have "?A m' \<subset> ?A m"
          proof
            show "?A m' \<noteq> ?A m" using m' by auto
            show "?A m' \<subseteq> ?A m" using m' dominates_antisymm[of m m'] dominates_trans[of m] by auto
          qed
          thus ?thesis by (rule psubset.IH[of _ m', simplified psubset.prems(1)], simp_all add: m')
        qed
      qed
    qed
    show "\<exists>m. isIdom n m" by (rule 1[of "?A (Entry)"], auto simp: assms(2)[symmetric])
  next
    fix m m'
    assume "isIdom n m" "isIdom n m'"
    thus "m = m'" by - (rule dominates_antisymm[of], auto simp:isIdom_def dest: dominator_in_\<alpha>n)
  qed

  lemma idom: "\<lbrakk>n \<in> set \<alpha>n - {Entry}\<rbrakk> \<Longrightarrow> isIdom n (idom n)"
  unfolding idom_def by (rule theI', rule idom_ex, auto)

  lemma dominates_mid:
    assumes "dominates n x" "dominates x m" "n\<comment>ns\<rightarrow>m"
    shows "x \<in> set ns"
  using assms
  proof (cases "n = x")
    case False
    from assms(1) obtain ns\<^sub>0 where ns\<^sub>0: "Entry\<comment>ns\<^sub>0\<rightarrow>n" "n \<notin> set (butlast ns\<^sub>0)" by - (rule simple_Entry_path, auto)
    with assms(3) have "Entry\<comment>butlast ns\<^sub>0@ns\<rightarrow>m" by auto
    with assms(2) have "x \<in> set (butlast ns\<^sub>0@ns)" by (auto elim!:dominatesE)
    moreover have "x \<notin> set (butlast ns\<^sub>0)"
    proof
      assume asm: "x \<in> set (butlast ns\<^sub>0)"
      with ns\<^sub>0 obtain ns\<^sub>0' where ns\<^sub>0': "Entry\<comment>ns\<^sub>0'\<rightarrow>x" "n \<notin> set (butlast ns\<^sub>0')"
        by - (erule path2_split_ex, auto dest:in_set_butlastD simp: butlast_append split: split_if_asm)
      show False by (metis False assms(1) ns\<^sub>0' strict_domE)
    qed
    ultimately show ?thesis by simp
  qed auto

  definition shortestPath :: "'node \<Rightarrow> nat" where
    "shortestPath n \<equiv> (LEAST l. \<exists>ns. length ns = l \<and> Entry\<comment>ns\<rightarrow>n)"

  lemma shortestPath_ex:
    assumes "n \<in> set \<alpha>n"
    obtains ns where "Entry\<comment>ns\<rightarrow>n" "distinct ns" "length ns = shortestPath n"
  proof-
    from assms obtain ns where "Entry\<comment>ns\<rightarrow>n" by - (atomize_elim, rule Entry_reaches)
    then obtain sns where sns: "length sns = shortestPath n" "Entry\<comment>sns\<rightarrow>n"
      unfolding shortestPath_def
      by -(atomize_elim, rule LeastI, auto)
    then obtain sns' where sns': "length sns' \<le> shortestPath n" "Entry\<comment>sns'\<rightarrow>n" "distinct sns'" by - (rule simple_path2, auto)
    moreover from sns'(2) have "shortestPath n \<le> length sns'" unfolding shortestPath_def by - (rule Least_le, auto)
    ultimately show thesis by -(rule that, auto)
  qed

  lemma[simp]: "\<lbrakk>n \<in> set \<alpha>n\<rbrakk> \<Longrightarrow> shortestPath n \<noteq> 0"
    by (metis length_0_conv path2_not_Nil2 shortestPath_ex)

  lemma shortestPath_upper_bound:
    assumes "n \<in> set \<alpha>n"
    shows "shortestPath n \<le> length \<alpha>n"
  proof-
    from assms obtain ns where ns: "Entry\<comment>ns\<rightarrow>n" "length ns = shortestPath n" "distinct ns" by (rule shortestPath_ex)
    hence "shortestPath n = length ns" by simp
    also have "... = card (set ns)" using ns(3) by (rule distinct_card[symmetric])
    also have "... \<le> card (set \<alpha>n)" using ns(1) by - (rule card_mono, auto)
    also have "... \<le> length \<alpha>n" by (rule card_length)
    finally show ?thesis .
  qed

  lemma shortestPath_predecessor_ex:
    assumes "n \<in> set \<alpha>n - {Entry}"
    obtains n' where "Suc (shortestPath n') = shortestPath n" "n' \<in> set (predecessors n)"
  proof -
    from assms obtain sns where sns: "length sns = shortestPath n" "Entry\<comment>sns\<rightarrow>n"
      by - (rule shortestPath_ex, auto)
    let ?n' = "last (butlast sns)"
    from assms(1) sns(2) have 1: "length sns \<ge> 2" by auto
    hence prefix: "Entry\<comment>butlast sns\<rightarrow>last (butlast sns) \<and> last (butlast sns) \<in> set (predecessors n)"
      using sns by -(rule path2_unsnoc, auto)
    hence "shortestPath ?n' \<le> length (butlast sns)"
      unfolding shortestPath_def by -(rule Least_le, rule exI[where x = "butlast sns"], simp)
    with 1 sns(1) have 2: "shortestPath ?n' < shortestPath n" by auto
    { assume asm: "Suc (shortestPath ?n') \<noteq> shortestPath n"
      obtain sns' where sns': "Entry\<comment>sns'\<rightarrow>?n'" "length sns' = shortestPath ?n'"
        using prefix by - (rule shortestPath_ex, auto)
      hence[simp]: "Entry\<comment>sns'@[n]\<rightarrow>n" using prefix by auto
      from asm 2 have "Suc (shortestPath ?n') < shortestPath n" by auto
      from this[unfolded shortestPath_def, THEN not_less_Least, folded shortestPath_def, simplified, THEN spec[of _ "sns'@[n]"]]
      have False using sns'(2) by auto
    }
    with prefix show thesis by - (rule that, auto)
  qed

  lemma shortestPath_single_predecessor: "predecessors n = [n'] \<Longrightarrow> shortestPath n' < shortestPath n"
    by (rule shortestPath_predecessor_ex[of n], auto intro: successor_is_node)

  lemma successor_in_\<alpha>n:
    assumes "predecessors n \<noteq> []"
    shows "n \<in> set \<alpha>n"
  proof-
    from assms(1) obtain m where "m \<in> set (predecessors n)" by (cases "predecessors n", auto)
    with assms(1) obtain m' e where "(m',e,n) \<in> \<alpha>e" using inEdges_correct[of n]
      by (auto simp: inEdges_def simp del: inEdges_correct)
    with assms(1) show ?thesis
      by auto
  qed

  lemma empty_preds_of_nonnode: "n \<notin> set \<alpha>n \<Longrightarrow> predecessors n = []"
    using successor_in_\<alpha>n by auto

  lemma strict_dom_shortestPath_order:
    assumes "strict_dom n m" "m \<in> set \<alpha>n"
    shows "shortestPath n < shortestPath m"
  proof-
    from assms(2) obtain sns where sns: "Entry\<comment>sns\<rightarrow>m" "length sns = shortestPath m"
      by (rule shortestPath_ex)
    with assms(1) sns(1) obtain sns' where sns': "Entry\<comment>sns'\<rightarrow>n" "prefixeq sns' sns" by -(erule path2_prefix_ex, auto elim:dominatesE)
    hence "shortestPath n \<le> length sns'"
      unfolding shortestPath_def by -(rule Least_le, auto)
    also have "length sns' < length sns"
    proof-
      from assms(1) sns(1) sns'(1) have "sns' \<noteq> sns" by -(drule path2_last, drule path2_last, auto)
      with sns'(2) have "prefix sns' sns" by auto
      thus ?thesis by (rule prefixeq_length_less)
    qed
    finally show ?thesis by (simp add:sns(2))
  qed

  lemma dominates_shortestPath_order:
    assumes "dominates n m" "m \<in> set \<alpha>n"
    shows "shortestPath n \<le> shortestPath m"
  using assms by (cases "n = m", auto intro:strict_dom_shortestPath_order[THEN less_imp_le])

  lemma strict_dom_trans:
    assumes "strict_dom n m" "strict_dom m m'"
    shows "strict_dom n m'"
  proof (rule, rule notI)
    assume "n = m'"
    moreover from assms(2) have "m' \<in> set \<alpha>n" by auto
    ultimately have "dominates m' n" by auto
    with assms(1) have "dominates m' m" by - (rule dominates_trans, auto)
    with assms(2) show False by - (erule conjE, drule dominates_antisymm, auto)
  next
    from assms show "dominates n m'" by - (rule dominates_trans, auto)
  qed

  inductive EntryPath :: "'node list \<Rightarrow> bool" where
    EntryPath_triv[simp]: "EntryPath [n]"
  | EntryPath_snoc[intro]: "EntryPath ns \<Longrightarrow> shortestPath m = Suc (shortestPath (last ns)) \<Longrightarrow> EntryPath (ns@[m])"

  lemma EntryPath_prefixeq:
    assumes "EntryPath ns" "prefixeq ns' ns" "ns' \<noteq> []"
    shows "EntryPath ns'"
  using assms proof induction
    case (EntryPath_triv ns)
    thus ?case by (cases ns', auto)
  qed auto

  lemma EntryPath_suffixeq:
    assumes "EntryPath ns" "suffixeq ns' ns" "ns' \<noteq> []"
    shows "EntryPath ns'"
  using assms proof (induction arbitrary: ns')
    case EntryPath_triv
    thus ?case
      by (metis EntryPath.EntryPath_triv append_Nil append_is_Nil_conv list.sel(3) suffixeq_def tl_append2)
  next
    case (EntryPath_snoc ns m)
    from EntryPath_snoc.prems obtain ns'' where [simp]: "ns' = ns''@[m]"
      by - (erule suffixeq_unsnoc, auto)
    show ?case
    proof (cases "ns'' = []")
      case True
      thus ?thesis by auto
    next
      case False
      from EntryPath_snoc.prems(1) have "suffixeq ns'' ns" by (auto simp: suffixeq_def)
      with False have "last ns'' = last ns" by (auto simp: suffixeq_def)
      moreover from False have "EntryPath ns''" using EntryPath_snoc.prems(1)
        by - (rule EntryPath_snoc.IH, auto simp: suffixeq_def)
      ultimately show ?thesis using EntryPath_snoc.hyps(2)
        by - (simp, rule EntryPath.EntryPath_snoc, simp_all)
    qed
  qed

  lemma EntryPath_butlast_less_last:
    assumes "EntryPath ns" "z \<in> set (butlast ns)"
    shows "shortestPath z < shortestPath (last ns)"
  using assms proof (induction)
    case (EntryPath_snoc ns m)
    thus ?case by (cases "z \<in> set (butlast ns)", auto dest: not_in_butlast)
  qed simp

  lemma Entry_reachesE:
    assumes "n \<in> set \<alpha>n"
    obtains ns where "Entry\<comment>ns\<rightarrow>n" "EntryPath ns"
  using assms(1) proof (induction "shortestPath n" arbitrary:n)
    case 0
    hence False by simp
    thus ?case..
  next
    case (Suc l)
    note Suc.prems(2)[simp]
    show ?case
    proof (cases "n = Entry")
      case True
      thus ?thesis by - (rule Suc.prems(1), auto)
    next
      case False
      then obtain n' where n': "shortestPath n' = l" "n' \<in> set (predecessors n)"
        using Suc.hyps(2)[symmetric] by - (rule shortestPath_predecessor_ex, auto)
      moreover {
        fix ns
        assume asm: "Entry\<comment>ns\<rightarrow>n'" "EntryPath ns"
        hence thesis using n' Suc.hyps(2) path2_last[OF asm(1)]
          by - (rule Suc.prems(1)[of "ns@[n]"], auto)
      }
      ultimately show thesis by - (rule Suc.hyps(1), auto)
    qed
  qed
end

end

