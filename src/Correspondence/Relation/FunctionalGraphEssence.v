Require Export
  Bourbaki.Correspondence.Term.Graph
  Bourbaki.Equality.Relation.AtMostOneExistence.

(* Def_E_II_3__9_i / G est un graphe fonctionnel / G est une famille *)
Definition is_functional_graph
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} (G : Graph) :=
∀ x, at_most_one_existence (fun y => ❨x, y❩ ∈ G).