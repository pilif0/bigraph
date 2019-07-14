(*  Title:       Graph.thy
    Author:      Filip Smola, 2019
*)

section\<open>Graphs\<close>
text\<open>The graph theory required to define bigraphs and their constituents.
Focused on forests (for place graphs) and hypergraphs (for link graphs).

Heavily inspired by Tom Ridge's 2005 paper "Graphs and Trees in Isabelle/HOL".\<close>

theory Graph
  imports
    Main
begin

subsection\<open>Paths and Edges\<close>

text\<open>A path is a list of nodes with some extra conditions. The extra conditions are introduced in a
later subsection.\<close>
type_synonym 'a prepath = "'a list"

text\<open>An edge is a set of one or more connected nodes.\<close>
type_synonym 'a edge = "'a set"

text\<open>A pre-path gives rise to a list of edges.\<close>
primrec edge_list :: "'a prepath \<Rightarrow> 'a edge list"
  where
    "edge_list [] = []"
  | "edge_list (x#xs) = (case xs of
        [] \<Rightarrow> []
      | (y#ys) \<Rightarrow> ({x,y}#(edge_list xs)))"

text\<open>A path is loop-free if its generated edge list contains no loops (i.e. edges \<open>{x,x}\<close>).\<close>
definition is_loop_free :: "'a prepath \<Rightarrow> bool"
  where "is_loop_free p = (\<forall>x . {x,x} \<notin> set (edge_list p))"

subsection\<open>Graphs and Subgraphs\<close>

text\<open>A graph is a record with a set of vertices and a set of edges.\<close>
record 'a pregraph =
  Verts :: "'a set"
  Edges :: "'a edge set"

(*TODO paper suggests defining the next two on pregraph instead of pregraph_scheme*)
text\<open>A graph is well-formed iff its edge set is a subset of the powerset of the vertices and
contains no loops.\<close>
definition is_graph :: "('a,'b) pregraph_scheme \<Rightarrow> bool"
  where "is_graph g = (Edges g \<subseteq> Pow (Verts g) \<and> (\<forall>x. {x,x} \<notin> (Edges g)))"

text\<open>A graph G is a subgraph of a graph H iff the vertex and edge sets of G are subsets of those of
H.\<close>
definition is_subgraph :: "('a,'b) pregraph_scheme \<Rightarrow> ('a,'c) pregraph_scheme \<Rightarrow> bool"
  where "is_subgraph G H = (Verts G \<subseteq> Verts H \<and> Edges G \<subseteq> Edges H)"

subsection\<open>Paths Continued\<close>

text\<open>A path consists of a set of vertices and gives rise to a set of edges, therefore it represents
a graph.\<close>
definition graph_of :: "'a prepath \<Rightarrow> 'a pregraph"
  where "graph_of p = \<lparr> Verts = set p, Edges = set (edge_list p) \<rparr>"

text\<open>A path lies in a graph G if its graph is a subgraph of G. Therefore we do not require a special
predicate for that.\<close>

text\<open>We constrain the type of prepaths with the following properties:
  * The empty list does not represent a valid path,
  * A path should be loop-free (which respects the restriction placed on graphs)
This most general form of a path is called a walk.\<close>
definition is_walk :: "'a prepath \<Rightarrow> bool"
  where "is_walk p = (p \<noteq> [] \<and> is_loop_free p)"

text\<open>A trail is a walk whose all edges are distinct.\<close>
definition is_trail :: "'a prepath \<Rightarrow> bool"
  where "is_trail p = (is_walk p \<and> distinct (edge_list p))"

(* Deviation from source: I note length constraints of circuits as lemmas instead of including them
in the circuit definition. *)
text\<open>A circuit is a trail whose start and end vertices are the same and which contains at least one
edge.\<close>
definition is_circuit :: "'a prepath \<Rightarrow> bool"
  where "is_circuit p = (is_trail p \<and> hd p = last p \<and> length (edge_list p) > 0)"

text\<open>A circuit can't be of length 0 because walks can't be empty.
It can't be of length 1 because it has to contain an edge.
It can't be of length 2 because walks are loop-free.
It can't be of length 3 because edges have to be distinct (i.e. not \<open>{x,y}\<close> and \<open>{y,x}\<close>).\<close>
lemma circuit_length:
  assumes circ: "is_circuit p"
  shows "length p > 3"
proof -
  have l0: "length p \<noteq> 0"
    using circ is_circuit_def is_trail_def is_walk_def by blast

  moreover have "length p \<noteq> 1"
  proof (rule ccontr)
    assume "\<not>length p \<noteq> 1"
    then have "length p = 1"
      by simp
    then have "\<exists>x. p = [x]"
      using length_0_conv length_Suc_conv One_nat_def by metis
    then obtain x where "p = [x]"
      by auto
    then have "edge_list p = []"
      by simp
    then have "length (edge_list p) = 0"
      by simp
    then show "False"
      using circ is_circuit_def by blast
  qed

  moreover have "length p \<noteq> 2"
  proof (rule ccontr)
    assume "\<not>length p \<noteq> 2"
    then have "length p = 2"
      by simp
    then have "\<exists>x y. p = [x,y]"
      using length_0_conv length_Suc_conv One_nat_def Suc_1 by metis
    then obtain x y where cont_p: "p = [x,y]" and "hd p = x" and "last p = y"
      by auto
    then have "x = y"
      using is_circuit_def circ by metis
    moreover have "edge_list p = [{x,y}]"
      using cont_p by simp
    ultimately have "\<not>is_loop_free p"
      by (simp add: is_loop_free_def)
    then show "False"
      using circ is_circuit_def is_trail_def is_walk_def by blast
  qed

  moreover have "length p \<noteq> 3"
  proof (rule ccontr)
    assume "\<not>length p \<noteq> 3"
    then have "length p = 3"
      by simp
    then have "\<exists>x y z. p = [x,y,z]"
      using length_0_conv length_Suc_conv numeral_3_eq_3 by smt
    then obtain x y z where cont_p: "p = [x,y,z]" and "hd p = x" and "last p = z"
      by auto
    then have "x = z"
      using is_circuit_def circ by metis
    then have "{x,y} = {y,z}"
      by (simp add: insert_commute)
    moreover have "edge_list p = [{x,y},{y,z}]"
      using cont_p by simp
    ultimately have "\<not>distinct (edge_list p)"
      by simp
    then show "False"
      using circ is_circuit_def is_trail_def by blast
  qed

  moreover have "length p \<ge> 0"
    by simp

  ultimately show "length p > 3"
    by (simp add: Suc_lessI numeral_3_eq_3)
qed

text\<open>A path is a trail whose vertices are distinct.\<close>
definition is_path :: "'a prepath \<Rightarrow> bool"
  where "is_path p = (is_trail p \<and> distinct p)"

text\<open>If the vertices are distinct, then the edge list is also distinct.\<close>
lemma vertices_distinct_then_edges:
  assumes "distinct (p :: 'a prepath)"
  shows "distinct (edge_list p)"
proof (cases "length p < 2")
  (* Trivial for zero, one vertices *)
  case True
  then have "length p = 0 \<or> length p = 1"
    by (simp add: less_Suc_eq numeral_2_eq_2)
  then have "p = [] \<or> (\<exists>x. p = [x])"
      using length_0_conv length_Suc_conv One_nat_def Suc_1 by metis
  then have "edge_list p = []"
    by auto
  then show ?thesis
    by simp
next
  case geq: False
  then show ?thesis
  proof (cases "length p = 2")
    (* Still simple with two vertices giving rise to one edge. *)
    case True
    then have "\<exists>x y. p = [x,y]"
      using length_0_conv length_Suc_conv One_nat_def Suc_1 by metis
    then obtain x y where cont_p: "p = [x, y]"
      by auto
    then have "edge_list p = [{x,y}]"
      by simp
    then show "distinct (edge_list p)"
      by simp
  next
    (* If edge list wasn't distinct, there would be two edges {a,b} in it and those can only arise by
having two sequences of a followed by b in the vertex list. *)
    case False
    then have ge: "length p > 2"
      using geq by simp
    show ?thesis
    proof (rule ccontr)
      assume "\<not>distinct (edge_list p)"
      then have "\<exists>a b l r. edge_list p = l@{a,b}#r \<and> distinct l \<and> {a,b} \<in> set r"
        sorry
      show "False" sorry
    qed
  qed
qed

text\<open>We can then derive an alternative definition of a path as a non-empty distinct list.\<close>
lemma is_path_def_2: "is_path p = (p \<noteq> [] \<and> distinct p)"
  sorry

text\<open>We define a cycle as a circuit whose vertices are distinct, except for the first and last.\<close>
definition is_cycle :: "'a prepath \<Rightarrow> bool"
  where "is_cycle p = (is_circuit p \<and> is_path (tl p))"

text\<open>We can also derive a cycle definition removing some redundancy.\<close>
lemma is_cycle_def_2: "is_cycle p = (hd p = last p \<and> distinct (tl p) \<and> length (edge_list p) > 0)"
  sorry
end