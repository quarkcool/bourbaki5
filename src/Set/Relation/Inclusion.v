Require Export
  Bourbaki.Quantification.Relation.TypicalUniversality
  Bourbaki.Set.Syntax.

(* Def_E_II_1__1 / relation d'inclusion *)
Definition inclusion `{Set_.Syntax} X Y := ∀ x ⟨∈ X⟩, x ∈ Y.

Notation "y ⊃ x" := (inclusion x y) : bourbaki_scope.

Notation "x ⊂ y" := (y ⊃ x) : bourbaki_scope.