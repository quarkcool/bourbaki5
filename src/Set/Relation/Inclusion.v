Require Export
  Bourbaki.Quantification.Relation.TypicalUniversality
  Bourbaki.Set.Syntax.

(* DEF1 / relation d'inclusion *)
Definition inclusion `{Set_.Syntax} x y := ∀ z ⟨ ∈ x ⟩, z ∈ y.
Hint Transparent inclusion : introduction_pattern_instances.

Notation "y ⊃ x" := (inclusion x y) : bourbaki_scope.

Notation "x ⊂ y" := (y ⊃ x) : bourbaki_scope.