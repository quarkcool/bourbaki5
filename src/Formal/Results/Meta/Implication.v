Require Export
  Bourbaki.Formal.ImplicationProof
  Bourbaki.Meta.Tactic.Revert
  Bourbaki.Meta.Tactic.Rewrite.

Module Implication.
  Section Implication.
    Context `{Formal.Theory}.

    #[export]
    Instance : Morphisms.Params (@ImplicationProof) 2 := ltac2:(split).

    Fact entailment
      {T 𝐀 𝐁} {H₁ : SolveLater _} {H₂ : ⊢ 𝐀 ⇒ 𝐁}
      `(Entailment _ false (Formal.syllogism H₁ H₂) T) :
        Entailment false H₂ T.
    Proof.
      repeat split.
      Apply _.
    Defined.

    Fact rewrite_lemma {𝐀 𝐁} (H₁ : 𝐀 ⊢⇒ 𝐁) :
      RewriteLemma H₁ (𝐀 ⊢⇒ 𝐁).
    Proof.
      split.
      Assumption.
    Defined.

    Fact rewrite_lemma₂
      {T 𝐀 𝐁} {H₁ : ⊢ 𝐀 ⇒ 𝐁}
      `(lem : forall H₂, RewriteLemma (Formal.syllogism H₂ H₁) T) :
        RewriteLemma H₁ ((⊢ 𝐀) -> T).
    Proof.
      split.
      Intros H₂.
      Apply (lem H₂).(Rewrite.rewrite_lemma).
    Defined.
  End Implication.

  Hint Resolve entailment | 2 : entailment_instances.

  Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.

  Hint Resolve rewrite_lemma₂ | 2 : rewrite_lemma_instances.

  Section Implication.
    Context `{Formal.Theory}.

    #[export]
    Instance :
      Morphisms.Proper
        (ImplicationProof --> Basics.flip Basics.impl)
        Formal.Proof
    | 0.
    Proof.
      Intros 𝐁 𝐀 H₁ H₂; unfold Basics.flip in *.
      Apply H₁.
      Assumption.
    Qed.

    Fact meta_introduction_pattern
      {cat 𝐀 𝐁}
      `(!Ununifiable cat fresh_pattern)
      `(pat : !IntroductionPattern cat (⊢ 𝐀 ⇒ 𝐁)) :
        IntroductionPattern cat ((⊢ 𝐀) -> ⊢ 𝐁).
    Proof.
      esplit.
      Intros H₁ H₂.
      Apply pat.(Intros.introduction_pattern);
        Assumption.
    Defined.

    Fact revert {𝐀} 𝐁 (H₁ : ⊢ 𝐀) :
      Revert H₁ (⊢ 𝐁).
    Proof.
      esplit.
      Intros H₂.
      Apply (_ : ⊢ 𝐀 ⇒ 𝐁);
        Assumption.
    Defined.
  End Implication.

  Hint Resolve meta_introduction_pattern | 0 : introduction_pattern_instances.

  Hint Resolve revert | 0 : revert_instances.
End Implication.
Export (hints) Implication.