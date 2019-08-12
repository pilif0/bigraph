(*  Title:       Hypergraph.thy
    Author:      Filip Smola, 2019
*)

section\<open>Hypergraphs\<close>
text\<open>Theory of hypergraphs, a generalization of graphs where an edge can connect any number of
vertices.
In the following, any mention of graph refers to a hypergraph.
Moreover, we assume that the vertices and edges of the hypergraphs are finite.

Inspired by Tom Ridge's 2005 paper "Graphs and Trees in Isabelle/HOL".\<close>

theory Hypergraph
  imports
    Main
begin

text\<open>Hypergraph is a pair \<open>(Verts, Edges)\<close> where \<open>Verts\<close> is a set of vertices and \<open>Edges\<close> is a set of
non-empty subsets of \<open>Verts\<close> called edges.\<close>
(* Basic datatype: *)
codatatype 'v pre_hypergraph = Hypergraph (Verts: "'v set") (Edges: "('v set) set")

lemma pre_hypergraph_eq_iff: "x = y \<longleftrightarrow> ((Verts x = Verts y) \<and> (Edges x = Edges y))"
  using pre_hypergraph.expand by auto

(* Actual hypergraph: *)
locale hypergraph =
  fixes hg :: "'v pre_hypergraph"
  assumes
    (* Vertices and edges have to be finite sets for some of the theorems to be provable *)
    vertices_finite: "finite (Verts hg)" and
    edges_finite: "finite (Edges hg)" and

    (* Edges are non-empty *)
    edges_not_empty: "{} \<notin> Edges hg" and

    (* Edges are subsets of the vertices *)
    edges_in_powerset: "\<forall>e. e \<in> Edges hg \<longrightarrow> (e \<subseteq> Verts hg)"
begin

text\<open>Edges are non-empty, therefore their cardinality is at least 1.\<close>
lemma edges_card:
  assumes "hypergraph hg"
  shows "\<forall>e. e \<in> Edges hg \<longrightarrow> card e \<ge> 1"
proof (rule allI, rule impI)
  fix e assume edge: "e \<in> Edges hg"
  then have "e \<noteq> {}"
    using edges_not_empty by auto
  moreover have "finite e"
    using edge edges_in_powerset infinite_super vertices_finite by blast
  ultimately show "card e \<ge> 1"
    by (simp add: Suc_leI card_gt_0_iff)
qed

text\<open>Intersection of an edge with the vertices is the edge.
This is just a restatement of the fact that edges are subsets of vertices.\<close>
lemma edge_inter_vertices: "e \<in> Edges hg \<Longrightarrow> e \<inter> Verts hg = e"
  by (simp add: edges_in_powerset inf.absorb1)

end

subsection\<open>Properties\<close>

text\<open>A hypergraph is loop free if it contains no singleton edges.\<close>
definition loop_free :: "'v pre_hypergraph \<Rightarrow> bool"
  where "loop_free hg = (\<forall>e. e \<in> Edges hg \<longrightarrow> (card e \<noteq> 1))"

text\<open>A loop free hypergraph has all edges of cardinality at least 2.\<close>
lemma loop_free_card:
  assumes "hypergraph hg"
      and "loop_free hg"
  shows "\<forall>e. e \<in> Edges hg \<longrightarrow> card e \<ge> 2"
  using assms(1) assms(2) hypergraph.edges_card loop_free_def by fastforce

text\<open>Empty hypergraph has no vertices and no edges.\<close>
definition is_empty :: "'v pre_hypergraph \<Rightarrow> bool"
  where "is_empty hg = (Verts hg = {} \<and> Edges hg = {})"

text\<open>Trivial hypergraph can have vertices, but no edges.\<close>
(* Deviation from literature: I allow a trivial hypergraph to be empty. This should simplify later
statements, removing need to separately state \<open>is_trivial hg \<or> is_empty hg\<close>. This should be revised
at a later date as it might possibly break some things. *)
definition is_trivial :: "'v pre_hypergraph \<Rightarrow> bool"
  where "is_trivial hg = (Edges hg = {})"

lemma empty_is_trivial:
  assumes "is_empty hg"
  shows "is_trivial hg"
  by (meson Hypergraph.is_empty_def assms is_trivial_def)

text\<open>A k-uniform hypergraph has all edges of cardinality k.\<close>
definition is_k_uniform :: "nat \<Rightarrow> 'v pre_hypergraph \<Rightarrow> bool"
  where "is_k_uniform k hg = (\<forall>e. e \<in> Edges hg \<longrightarrow> card e = k)"

text\<open>Simple hypergraph has no nested hyperedges.\<close>
definition is_simple :: "'v pre_hypergraph \<Rightarrow> bool"
  where "is_simple hg = (\<forall>e f. e \<in> Edges hg \<and> f \<in> Edges hg \<and> e \<subseteq> f \<longrightarrow> e = f)"

text\<open>Degree of a vertex is the number of edges containing it.\<close>
definition degree :: "'v \<Rightarrow> 'v pre_hypergraph \<Rightarrow> nat"
  where "degree v hg = card {e | e. e \<in> Edges hg \<and> v \<in> e}"

text\<open>A k-regular hypergraph has all vertices of degree k.\<close>
definition is_k_regular :: "nat \<Rightarrow> 'v pre_hypergraph \<Rightarrow> bool"
  where "is_k_regular k hg = (\<forall>v. v \<in> Verts hg \<longrightarrow> degree v hg = k)"

subsection\<open>Subhypergraphs\<close>

text\<open>Subhypergraph A of hypergraph B is a hypergraph formed from B by removing some vertices from
both its vertex set and edges. Because A is a hypergraph, any empty edges are also removed.\<close>
definition is_subhg_of :: "'v pre_hypergraph \<Rightarrow> 'v pre_hypergraph \<Rightarrow> bool"
  (* Hypergraph condition is only on the source is sufficient, because this implies that the result
      is a hypergraph as well *)
  where "is_subhg_of a b = (hypergraph b \<longrightarrow> (Verts a \<subseteq> Verts b \<and>
                                              Edges a = ({e \<inter> Verts a | e. e \<in> Edges b} - {{}})))"

(* Subhypergraph introduction rule for hypergraph sources *)
lemma is_subhg_ofI:
  assumes "hypergraph b"
      and "Verts a \<subseteq> Verts b"
      and "Edges a = ({e \<inter> Verts a | e. e \<in> Edges b} - {{}})"
    shows "is_subhg_of a b"
  by (simp add: assms(2) assms(3) is_subhg_of_def)


text\<open>Any subhypergraph of a hypergraph is itself a hypergraph.\<close>
lemma subhg_is_hypergraph:
  assumes "is_subhg_of a b"
      and "hypergraph b"
    shows "hypergraph a"
proof
  show "finite (Verts a)"
    using assms(1) assms(2) hypergraph.vertices_finite infinite_super is_subhg_of_def by blast
  show "finite (Edges a)"
  proof -
    have "finite (Edges b)"
      by (simp add: assms(2) hypergraph.edges_finite)
    then have "\<forall>S. finite ({e \<inter> S | e. e \<in> Edges b} - {{}})"
      by simp
    moreover have "Edges a = {e \<inter> Verts a | e. e \<in> Edges b} - {{}}"
      using assms(1) assms(2) is_subhg_of_def by blast
    ultimately show ?thesis
      by simp
  qed
  show no_empty_edge: "{} \<notin> Edges a"
    using assms(1) assms(2) is_subhg_of_def by auto
  show "\<forall>e. e \<in> Edges a \<longrightarrow> e \<subseteq> Verts a"
  proof (rule allI, rule impI)
    fix e assume e_in_a: "e \<in> Edges a"
    then have "e \<noteq> {}"
      using no_empty_edge by blast
    then have source_edge: "\<exists>f. f \<in> Edges b \<and> e \<subseteq> f"
    proof -
      have "{f \<inter> Verts a |f. f \<in> Edges b} - {{}} = Edges a"
        using assms(1) assms(2) is_subhg_of_def by blast
      then have "\<forall>f. f \<in> Edges a \<longrightarrow> (\<exists>g. f = g \<inter> Verts a \<and> g \<in> Edges b)"
        by blast
      then show ?thesis
        using e_in_a by blast
    qed
    then have "e \<subseteq> Verts b"
      using assms(2) hypergraph.edge_inter_vertices by auto
    then show "e \<subseteq> Verts a"
    proof -
      have "{A \<inter> Verts a |A. A \<in> Edges b} - {{}} = Edges a"
        using assms(1) assms(2) is_subhg_of_def by blast
      then have "e \<in> {A \<inter> Verts a |A. A \<in> Edges b}"
        using e_in_a by blast
      then show ?thesis
        by fastforce
    qed
  qed
qed

text\<open>The subhypergraph predicate is reflexive.\<close>
lemma is_subhg_of_refl: "reflp is_subhg_of"
proof
  fix x :: "'v pre_hypergraph"
  show "is_subhg_of x x"
  proof (cases "hypergraph x")
    case True
    then have "Edges x = ({e \<inter> Verts x | e. e \<in> Edges x} - {{}})"
    proof -
      have "\<forall>e. e \<in> Edges x \<longrightarrow> e \<inter> Verts x = e"
        by (simp add: True hypergraph.edge_inter_vertices)
      then have "Edges x = {e \<inter> Verts x | e. e \<in> Edges x}"
        by auto
      moreover have "{} \<notin> Edges x"
        by (simp add: True hypergraph.edges_not_empty)
      ultimately show ?thesis
        by blast
    qed
    moreover have "Verts x \<subseteq> Verts x"
      by simp
    ultimately show ?thesis
      by (simp add: is_subhg_of_def)
  next
    case False
    then show ?thesis
      by (simp add: is_subhg_of_def)
  qed
qed

text\<open>The subhypergraph predicate is transitive.\<close>
lemma is_subhg_of_transp: "transp is_subhg_of"
proof
  fix x y z :: "'v pre_hypergraph"
  assume xy: "is_subhg_of x y" and yz: "is_subhg_of y z"
  then show "is_subhg_of x z"
  proof (cases "hypergraph z")
    case True
    then show ?thesis
    proof (rule is_subhg_ofI)
      have vx_in_vy: "Verts x \<subseteq> Verts y"
        using True is_subhg_of_def subhg_is_hypergraph xy yz by blast
      moreover have "Verts y \<subseteq> Verts z"
        using True is_subhg_of_def yz by blast
      ultimately show "Verts x \<subseteq> Verts z"
        by simp

      show "Edges x = {e \<inter> Verts x | e. e \<in> Edges z} - {{}}"
      proof
        (* Left to right *)
        have "Edges y = {e \<inter> Verts y | e. e \<in> Edges z} - {{}}"
          using True is_subhg_of_def yz by blast
        then have f_y: "\<forall>e. e \<in> Edges y \<longrightarrow> (\<exists>f. f \<in> Edges z \<and> e = f \<inter> Verts y) \<and> e \<noteq> {}"
          by auto

        have "Edges x = {e \<inter> Verts x | e. e \<in> Edges y} - {{}}"
          using True is_subhg_of_def subhg_is_hypergraph xy yz by blast
        then have f_x: "\<forall>e. e \<in> Edges x \<longrightarrow> (\<exists>f. f \<in> Edges y \<and> e = f \<inter> Verts x) \<and> e \<noteq> {}"
          by auto

        from f_x f_y have "\<forall>e. e \<in> Edges x \<longrightarrow> (\<exists>f. f \<in> Edges z \<and> e = f \<inter> Verts y \<inter> Verts x) \<and> e \<noteq> {}"
          by blast
        then have "\<forall>e. e \<in> Edges x \<longrightarrow> (\<exists>f. f \<in> Edges z \<and> e = f \<inter> Verts x) \<and> e \<noteq> {}"
          using vx_in_vy by auto
        then show "Edges x \<subseteq> {e \<inter> Verts x | e. e \<in> Edges z} - {{}}"
          by blast

        (* Right to left *)
        have "Edges y = {e \<inter> Verts y | e. e \<in> Edges z} - {{}}"
          using True is_subhg_of_def yz by blast
        then have f_y: "\<forall>e. e \<in> Edges z \<and> e \<inter> Verts y \<noteq> {} \<longrightarrow> e \<inter> Verts y \<in> Edges y"
          by blast

        have "Edges x = {e \<inter> Verts x | e. e \<in> Edges y} - {{}}"
          using True is_subhg_of_def subhg_is_hypergraph xy yz by blast
        then have f_x: "\<forall>e. e \<in> Edges y \<and> e \<inter> Verts x \<noteq> {} \<longrightarrow> e \<inter> Verts x \<in> Edges x"
          by blast

        from f_x f_y have "\<forall>e. e \<in> Edges z \<and> e \<inter> Verts y \<inter> Verts x \<noteq> {} \<longrightarrow> e \<inter> Verts y \<inter> Verts x \<in> Edges x"
          by blast
        then have "\<forall>e. e \<in> Edges z \<and> e \<inter> Verts x \<noteq> {} \<longrightarrow> e \<inter> Verts x \<in> Edges x"
          using vx_in_vy by (simp add: inf.absorb_iff2 inf_assoc)
        then show "{e \<inter> Verts x | e. e \<in> Edges z} - {{}} \<subseteq> Edges x"
          by blast
      qed
    qed
  next
    case False
    then show ?thesis
      by (simp add: is_subhg_of_def)
  qed
qed

text\<open>A set of vertices can induce a subhypergraph from a hypergraph.\<close>
primcorec induce_subhg :: "'v set \<Rightarrow> 'v pre_hypergraph \<Rightarrow> 'v pre_hypergraph"
  where
    "Verts (induce_subhg A hg) = A \<inter> Verts hg"
  | "Edges (induce_subhg A hg) = {e \<inter> A | e. e \<in> Edges hg} - {{}}"

(*TODO: better name?*)
lemma induce_subhg_result:
  assumes "hypergraph hg"
      and "s = induce_subhg A hg"
    shows "is_subhg_of s hg"
proof -
  have "\<forall>e . e \<in> Edges hg \<longrightarrow> (e \<inter> A = e \<inter> (A \<inter> Verts hg))"
    using assms(1) hypergraph.edge_inter_vertices by blast
  then have "{e \<inter> A | e. e \<in> Edges hg} = {e \<inter> (A \<inter> Verts hg) | e. e \<in> Edges hg}"
    by blast
  then show ?thesis
    by (simp add: assms(2) is_subhg_of_def)
qed

text\<open>Inducing a subhypergraph from a hypergraph produces a hypergraph.\<close>
lemma hypergraph_induced_subhg:
  assumes "s = induce_subhg A hg"
      and "hypergraph hg"
    shows "hypergraph s"
  using assms(1) assms(2) induce_subhg_result subhg_is_hypergraph by blast

text\<open>Inducing a subhypergraph with an empty set results in an empty hypergraph (with no vertices or
edges).\<close>
lemma empty_induced_subhg:
  assumes "s = induce_subhg A hg"
      and "A = {}"
    shows "s = Hypergraph {} {}"
proof -
  have "{e \<inter> {} |e. e \<in> Edges hg} \<subseteq> {{}}"
    by blast
  then show ?thesis
    by (simp add: assms(1) assms(2) induce_subhg.code)
qed

text\<open>Inducing a subhypergraph with the vertices of the hypergraph being induced upon results in the
original hypergraph.\<close>
(* Counter-examples for non-hypergraph hg:
 - If hg has edge {} then it is removed
 - If hg has edge e that is not subset of Verts hg then e will not be a subset of (Verts hg \<inter> A) *)
lemma identity_induced_subhg:
  assumes "s = induce_subhg A hg"
      and "hypergraph hg"
      and "A = Verts hg"
    shows "s = hg"
proof -
  have "Verts s = Verts hg"
    by (simp add: assms(1) assms(3))
  moreover have "Edges s = Edges hg"
  proof -
    have "\<forall>e. e \<in> Edges hg \<longrightarrow> e = e \<inter> A"
      by (simp add: assms(2) assms(3) hypergraph.edge_inter_vertices)
    then have "{e \<inter> A |e. e \<in> Edges hg} = {e | e. e \<in> Edges hg}"
      by blast
    then have "{e \<inter> A |e. e \<in> Edges hg} = Edges hg"
      by simp
    moreover have "{} \<notin> Edges hg"
      by (simp add: assms(2) hypergraph.edges_not_empty)
    ultimately show ?thesis
      by (simp add: assms(1))
  qed
  ultimately show ?thesis
    by (simp add: pre_hypergraph_eq_iff)
qed

(* TODO: extension of subhg *)

subsection\<open>Partial Hypergraph\<close>

text\<open>Partial hypergraph A is hypergraph B with some edges removed.\<close>
definition is_partial_of :: "'v pre_hypergraph \<Rightarrow> 'v pre_hypergraph \<Rightarrow> bool"
  where "is_partial_of a b = (Verts a = Verts b \<and> Edges a \<subseteq> Edges b)"

text\<open>Partial hypergraph of a hypergraph is itself a hypergraph.\<close>
lemma partial_is_hypergraph:
  assumes hg_b: "hypergraph b"
      and assm: "is_partial_of a b"
    shows "hypergraph a"
  by (metis assm hg_b hypergraph_def infinite_super is_partial_of_def subsetD)

text\<open>The partial hypergraph predicate is reflexive.\<close>
lemma is_partial_of_refl: "reflp is_partial_of"
  by (simp add: is_partial_of_def reflpI)

text\<open>The partial hypergraph predicate is transitive.\<close>
lemma is_partial_of_trans: "transp is_partial_of"
  by (metis (mono_tags, lifting) is_partial_of_def order_trans transp_def)

(*TODO would induction of a partial hypergraph with a subset of the edge index set be useful? *)