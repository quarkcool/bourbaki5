Require Export
  Bourbaki.Correspondence.Notation
  Bourbaki.Correspondence.Term.Graph
  Bourbaki.Quantification.Relation.TypicalExistence.

(* Def_E_II_3__3 / image de X par G *)
Definition image
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} (G : Graph) X :=
{y | ∃ x ⟨∈ X⟩, ❨x, y❩ ∈ G}.

Notation "G ⟨ X ⟩" := (image G X) : bourbaki_scope.