Require Export
  Bourbaki.Logic.Results.Meta.Logic
  Bourbaki.Quantification.Relation.Existence.

Section Existence.
  Context `{Logic.Theory}.

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
End Existence.

Hint Resolve destruction_pattern | 0 : introduction_pattern_instances.