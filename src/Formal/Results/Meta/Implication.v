Require Export
  Bourbaki.Formal.Meta.ImplicationMetaRelation
  Bourbaki.Meta.Tactic.Apply
  Bourbaki.Meta.Tactic.Rewrite.

Section Implication.
  Context `{Formal.Theory}.

  Definition entailment
    {𝐀} {H₁ : SolveLater _} {𝐁 H₂ 𝐂}
    `(Entailment (x := Formal.syllogism H₁ H₂) false (⊢ 𝐁) (⊢ 𝐂)) :
      Entailment (x := H₂) false (⊢ 𝐀 ⇒ 𝐁) (⊢ 𝐂).
  Proof.
    repeat split.
    Apply _.
  Defined.

  Definition rewrite_lemma {𝐀 𝐁} (H₁ : 𝐀 ⊢⇒ 𝐁) :
    RewriteLemma H₁ (𝐀 ⊢⇒ 𝐁) :=
  {| Rewrite.rewrite_lemma := H₁ |}.

  Definition rewrite_lemma₂
    {𝐀 𝐁} {H₁ : 𝐀 ⊢⇒ 𝐁} {T}
    `(lem : forall H₂, RewriteLemma (Formal.syllogism H₂ H₁) T) :
      RewriteLemma H₁ (⊢ 𝐀 -> T) :=
  {| Rewrite.rewrite_lemma := fun H₂ => (lem H₂).(Rewrite.rewrite_lemma) |}.
End Implication.

Hint Resolve entailment | 3 : entailment_instances.

Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.

Hint Resolve rewrite_lemma₂ | 2 : rewrite_lemma_instances.