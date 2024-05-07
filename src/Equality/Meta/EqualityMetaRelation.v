Require Export
  Bourbaki.Equality.Syntax
  Bourbaki.Formal.Proof.

Definition EqualityMetaRelation `{Equality.Syntax} 𝒯 x y := 𝒯 ⊢ x = y.

Notation "x ⊢⟨ 𝒯 ⟩= y" := (EqualityMetaRelation 𝒯 x y) : type_scope.

Module TheoryHidingNotation.
  Notation "x ⊢= y" := (x ⊢⟨_⟩= y) : type_scope.
End TheoryHidingNotation.