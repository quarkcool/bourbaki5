Require Export
  Bourbaki.Logic.Results.Meta.Equivalence
  Bourbaki.Quantification.Relation.Existence.

Module Existence.
  Section Existence.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem definition 𝐑 :
      ⊢ (∃ x, 𝐑 x) ⇔ 𝐑 (τ x, 𝐑 x).
    Proof.
      Rewrite Existence.unlock.
    Qed.

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
  End Existence.

  Hint Resolve destruction_pattern | 0 : introduction_pattern_instances.
End Existence.
Export (hints) Existence.