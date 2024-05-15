Require Export
  Bourbaki.Formal.Proof
  Bourbaki.Set.Relation.Inclusion.

Definition InclusionMetaRelation `{Set_.Syntax} 𝒯 x y := 𝒯 ⊢ x ⊂ y.
Hint Transparent InclusionMetaRelation : introduction_pattern_instances.

Notation "x ⊢⟨ 𝒯 ⟩⊂ y" := (InclusionMetaRelation 𝒯 x y) : type_scope.

Module TheoryHidingNotation.
  Notation "x ⊢⊂ y" := (x ⊢⟨_⟩⊂ y) : type_scope.
End TheoryHidingNotation.