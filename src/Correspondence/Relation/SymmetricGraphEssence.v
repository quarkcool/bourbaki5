Require Export
  Bourbaki.Correspondence.Term.ReverseGraph.

(* G est [un graphe] symétrique *)
Definition is_symmetric_graph
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} G :=
G⁻¹ = G.