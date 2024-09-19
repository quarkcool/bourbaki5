Require Export
  Bourbaki.Correspondence.Term.Graph
  Bourbaki.Correspondence.Term.RelationGraph.

(* Def_E_II_3__6 / composée de G₁ et G₂ *)
Definition graph_composite
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} (G₁ G₂ : Graph) :=
{❨x, z❩ | ∃ y, ❨x, y❩ ∈ G₂ ∧ ❨y, z❩ ∈ G₁}.

Infix "∘" := graph_composite : bourbaki_scope.