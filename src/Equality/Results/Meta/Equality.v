Require Export
  Bourbaki.Equality.Meta.EqualityMetaRelation
  Bourbaki.Formal.Results.Meta.StrongerTheoryEssence.

Section Equality.
  Context `{Equality.Syntax}.

  Definition rewrite_lemma {𝒯 x y} (H₁ : x ⊢⟨𝒯⟩= y) :
    RewriteLemma H₁ (x ⊢⟨𝒯⟩= y) :=
  {| Rewrite.rewrite_lemma := H₁ |}.
End Equality.

Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.