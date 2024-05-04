Require Export
  Bourbaki.Formal.Proof
  Bourbaki.Logic.Relation.Equivalence.

Definition EquivalenceMetaRelation `{Formal.Syntax} 𝒯 𝐀 𝐁 :=
𝒯 ⊢ 𝐀 ⇔ 𝐁.
Hint Transparent EquivalenceMetaRelation : introduction_pattern_instances.

Notation "𝐀 ⊢⟨ 𝒯 ⟩⇔ 𝐁" := (EquivalenceMetaRelation 𝒯 𝐀 𝐁) : type_scope.

Module TheoryHidingNotation.
  Notation "𝐀 ⊢⇔ 𝐁" := (𝐀 ⊢⟨_⟩⇔ 𝐁) : type_scope.
End TheoryHidingNotation.