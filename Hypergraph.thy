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

text\<open>A hypergraph is loop free if it contains no singleton edges.\<close>
definition loop_free :: "'v pre_hypergraph \<Rightarrow> bool"
  where "loop_free hg = (\<forall>e. e \<in> Edges hg \<longrightarrow> (card e \<noteq> 1))"

text\<open>A loop free hypergraph has all edges of cardinality at least 2.\<close>
lemma loop_free_card:
  assumes "hypergraph hg"
      and "loop_free hg"
  shows "\<forall>e. e \<in> Edges hg \<longrightarrow> card e \<ge> 2"
  using assms(1) assms(2) hypergraph.edges_card loop_free_def by fastforce

subsection\<open>Subhypergraphs\<close>

text\<open>Subhypergraph A of hypergraph B is a hypergraph formed from B by removing some vertices from
both its vertex set and edges. Because A is a hypergraph, it any empty edges are also removed.\<close>
definition is_subhypergraph :: "'v pre_hypergraph \<Rightarrow> 'v pre_hypergraph \<Rightarrow> bool"
  where "is_subhypergraph a b = (Verts a \<subseteq> Verts b \<and>
                                  (\<forall>e. e \<in> Edges a \<longrightarrow> (\<exists>f. f \<in> Edges b \<and> e = f \<inter> Verts a)
                                                        \<and> e \<noteq> {}))"

text\<open>A set of vertices can induce a subhypergraph from a hypergraph.\<close>
primcorec induce_subhypergraph :: "'v set \<Rightarrow> 'v pre_hypergraph \<Rightarrow> 'v pre_hypergraph"
  where
    "Verts (induce_subhypergraph A hg) = A \<inter> Verts hg"
  | "Edges (induce_subhypergraph A hg) = {e . (\<exists>f. f \<in> Edges hg \<and> e = f \<inter> A) \<and> e \<noteq> {}}"

(*TODO: better name?*)
lemma induce_subhypergraph_result:
  assumes "hypergraph hg"
      and "s = induce_subhypergraph A hg"
    shows "is_subhypergraph s hg"
(* One problem with this proof is equating Verts a with A in the edge part of the two definitions *)
  sorry

text\<open>Inducing a subhypergraph from a hypergraph produces a hypergraph.\<close>
lemma hypergraph_induced_subhypergraph:
  assumes "s = induce_subhypergraph A hg"
      and "hypergraph hg"
    shows "hypergraph s"
proof
  show "finite (Verts s)"
    by (simp add: assms(1) assms(2) hypergraph.vertices_finite)
  show "finite (Edges s)" sorry
  show "{} \<notin> Edges s"
    by (simp add: assms(1))
  show "\<forall>e. e \<in> Edges s \<longrightarrow> e \<subseteq> Verts s" sorry
qed

text\<open>Inducing a subhypergraph with an empty set results in an empty hypergraph (with no vertices or
edges).\<close>
lemma empty_induced_subhypergraph:
  assumes "s = induce_subhypergraph A hg"
      and "A = {}"
    shows "s = Hypergraph {} {}"
  by (simp add: assms(1) assms(2) induce_subhypergraph.code)

text\<open>Inducing a subhypergraph with the vertices of the hypergraph being induced upon results in the
original hypergraph.\<close>
lemma identity_induced_subhypergraph:
  assumes "s = induce_subhypergraph A hg"
      and "A = Verts hg"
    shows "s = hg"
proof -
  have "Verts s = Verts hg"
    by (simp add: assms(1) assms(2))
  moreover have "Edges s = Edges hg" sorry
  ultimately show ?thesis
    by (simp add: pre_hypergraph_eq_iff)
qed