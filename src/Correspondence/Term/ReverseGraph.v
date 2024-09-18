Require Export
  Bourbaki.Correspondence.Term.Graph
  Bourbaki.Correspondence.Term.RelationGraph.

(* Def_E_II_3__5 / graphe réciproque de G *)
Definition reverse_graph
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} (G : Graph) :=
{❨x, y❩ | ❨y, x❩ ∈ G}.

Notation "G ⁻¹" := (reverse_graph G) : bourbaki_scope.