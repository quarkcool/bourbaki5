Require Export
  Bourbaki.Logic.Results.Meta.Proof
  Bourbaki.Quantification.Theory.

Section Existence.
  Context `(QuantifiedTheory).

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

  Definition introduction_pattern 𝐑 (x : SolveLater Term) :
    IntroductionPattern complex_pattern (𝒯 ⊢ ∃ x, 𝐑 x).
  Proof.
    refine '{| Intros.NewGoals := 𝒯 ⊢ 𝐑 x |}.
    Intros H₁.
    Apply Quantification.existence_introduction.
    Assumption.
  Defined.
End Existence.

Hint Resolve destruction_pattern | 0 : introduction_pattern_instances.

Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.

Section Existence.
  Context `{Formal.Syntax}.

  Definition entailment
    {𝐑} `(NotEvar 𝐑) {T x 𝒯} y `{!LogicalTheory 𝒯} `(!QuantifiedTheory)
    `(Entailment true (x := x) T (𝒯 ⊢ 𝐑 y)) :
      Entailment (x := x) true T (𝒯 ⊢ Existence.existence 𝐑).
  Proof.
    split.
    { Apply Quantification.existence_introduction.
      Apply _. }
    { split. }
  Defined.
End Existence.

Hint Resolve entailment | 1 : entailment_instances.