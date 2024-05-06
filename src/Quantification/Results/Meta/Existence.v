Require Export
  Bourbaki.Logic.Results.Meta.Proof
  Bourbaki.Quantification.Relation.Existence.

Section Existence.
  Context `(LogicalTheory).

  Definition destruction_pattern 𝐑 𝐀 :
    IntroductionPattern complex_pattern (𝒯 ⊢ (∃ x, 𝐑 x) ⇒ 𝐀).
  Proof.
    refine '{| Intros.NewGoals := forall x, 𝒯 ⊢ 𝐑 x ⇒ 𝐀 |}.
    Intros H₁ H₂.
    Apply Proof.auxiliary_constant.
    { Assumption. }
    { Intros x.
      Apply H₁.
      Apply Proof.explicit_axiom.
      left.
      Reflexivity. }
  Defined.
End Existence.

Hint Resolve destruction_pattern | 0 : introduction_pattern_instances.