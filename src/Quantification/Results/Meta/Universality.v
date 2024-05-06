Require Export
  Bourbaki.Logic.Results.Negation
  Bourbaki.Quantification.Relation.Universality.

Section Universality.
  Context `(LogicalTheory).

  (* C26 *)
  Theorem alternative_definition 𝐑 :
    𝒯 ⊢ (∀ x, 𝐑 x) ⇔ 𝐑 (τ x, ¬𝐑 x).
  Proof.
    Apply Negation.double_removal.
  Defined.

  (* C27 *)
  Theorem introduction 𝐑 :
    (forall x, 𝒯 ⊢ 𝐑 x) -> 𝒯 ⊢ ∀ x, 𝐑 x.
  Proof.
    Intros H₁.
    Apply Universality.alternative_definition.
    Assumption.
  Defined.

  Definition introduction_pattern 𝐑 :
    IntroductionPattern simple_pattern (𝒯 ⊢ Universality.universality 𝐑) :=
  {| Intros.introduction_pattern := Universality.introduction _ |}.
End Universality.

Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.