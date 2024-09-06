Require Export
  Bourbaki.Logic.Results.Meta.Equivalence
  Bourbaki.Quantification.Theory.

Module Existence.
  Section Existence.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    Theorem definition 𝐑 :
      ⊢ (∃ x, 𝐑 x) ⇔ 𝐑 (τ x, 𝐑 x).
    Proof.
      Rewrite Existence.unlock.
    Qed.

    Fact introduction_pattern 𝐑 (x : SolveLater Term) :
      IntroductionPattern complex_pattern (⊢ existence 𝐑).
    Proof.
      esplit.
      Intros H₁.
      Apply (Quantification.existence_introduction _ x).
      Assumption.
    Defined.
  End Existence.

  Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.

  Section Existence.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    Theorem elimination 𝐑 𝐀 :
      (⊢ ∃ x, 𝐑 x) -> (forall x, (⊢ 𝐑 x) -> ⊢ 𝐀) -> ⊢ 𝐀.
    Proof.
      Rewrite Existence.definition.
      Apply Logic.auxiliary_constant.
    Qed.

    Fact destruction_pattern 𝐑 𝐀 :
      IntroductionPattern complex_pattern (⊢ existence 𝐑 ⇒ 𝐀).
    Proof.
      esplit with (NewGoals := forall x, ⊢ 𝐑 x ⇒ 𝐀).
      Intros H₁ H₂.
      Apply Existence.elimination.
      { Assumption. }
      { Intros x H₃.
        Apply H₁.
        Assumption. }
    Defined.

    Fact entailment
      {T 𝐑} {x : T} {y} `(NotEvar _ 𝐑) `(Entailment _ true x (⊢ 𝐑 y)) :
        Entailment true x (⊢ existence 𝐑).
    Proof.
      repeat split.
      Intros [].
      Assumption.
    Defined.
  End Existence.

  Hint Resolve entailment | 2 : entailment_instances.

  Hint Resolve destruction_pattern | 0 : introduction_pattern_instances.
End Existence.
Export (hints) Existence.