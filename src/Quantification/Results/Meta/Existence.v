Require Export
  Bourbaki.Logic.EquivalenceProof
  Bourbaki.Logic.Results.Meta.Conjunction
  Bourbaki.Quantification.Theory.

Section Existence.
  Context `{Quantification.Theory}.

  Fact introduction_pattern 𝐑 (x : SolveLater Formal.Term) :
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
  Context `{Quantification.Theory}.

  Theorem elimination 𝐑 𝐒 :
    (⊢ ∃ x, 𝐑 x) -> (forall x, (⊢ 𝐑 x) -> ⊢ 𝐒) -> ⊢ 𝐒.
  Proof.
    Intros H₁ H₂.
    Apply Logic.auxiliary_constant;
      Assumption.
  Qed.

  Fact destruction_pattern 𝐑 𝐒 :
    IntroductionPattern complex_pattern (⊢ existence 𝐑 ⇒ 𝐒).
  Proof.
    esplit with (NewGoals := forall x, ⊢ 𝐑 x ⇒ 𝐒).
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