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

end

text\<open>A hypergraph is loop free if it contains no singleton edges.\<close>
definition loop_free :: "'v pre_hypergraph \<Rightarrow> bool"
  where "loop_free hg = (\<forall>e. e \<in> Edges hg \<longrightarrow> (card e \<noteq> 1))"

text\<open>A loop free hypergraph has all edges of cardinality at least 2.\<close>
lemma loop_free_card:
  assumes "hypergraph hg" and "loop_free hg"
  shows "\<forall>e. e \<in> Edges hg \<longrightarrow> card e \<ge> 2"
  using assms(1) assms(2) hypergraph.edges_card loop_free_def by fastforce