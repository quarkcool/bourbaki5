Require Export
  Bourbaki.Set.Relation.Inclusion.

Definition non_inclusion `{Set_.Syntax} x y := ¬x ⊂ y.

Notation "y ⊅ x" := (non_inclusion x y) : bourbaki_scope.

Notation "x ⊄ y" := (y ⊅ x) : bourbaki_scope.