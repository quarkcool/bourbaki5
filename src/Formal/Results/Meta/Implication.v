Require Export
  Bourbaki.Formal.ImplicationProof
  Bourbaki.Meta.Tactic.Assumption
  Bourbaki.Meta.Tactic.Intros
  Bourbaki.Meta.Tactic.Rewrite.

Section Implication.
  Context `{Formal.Theory}.

  Fact entailment
    {T 𝐑 𝐒} {H₁ : SolveLater _} {H₂ : ⊢ 𝐑 ⇒ 𝐒}
    `(Entailment _ false (Formal.syllogism H₁ H₂) T) :
      Entailment false H₂ T.
  Proof.
    repeat split.
    Apply _.
  Defined.

  Fact rewrite_lemma {𝐑 𝐒} (H₁ : 𝐑 ⊢⇒ 𝐒) :
    RewriteLemma H₁ (𝐑 ⊢⇒ 𝐒).
  Proof.
    split.
    Assumption.
  Defined.
End Implication.

Hint Resolve entailment | 2 : entailment_instances.

Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.

Section Implication.
  Context `{Formal.Theory}.

  #[export]
  Instance :
    Morphisms.Proper (ImplicationProof --> Basics.flip Basics.impl) Formal.Proof
  | 0.
  Proof.
    Intros 𝐒 𝐑 H₁ H₂.
    Apply H₁.
    Assumption.
  Qed.
End Implication.