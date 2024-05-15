Require Export
  Bourbaki.Equality.Results.Meta.Rewriting
  Bourbaki.Quantification.Results.All
  Bourbaki.Set.Results.Meta.Inclusion
  Bourbaki.Set.Results.Theory.

Import Proof.TheoryHidingNotation.

Section Equality.
  Context `(SetTheory).

  Theorem alternative_definition₂ :
    𝒯 ⊢ ∀ x y, x = y ⇔ x ⊂ y ∧ y ⊂ x.
  Proof.
    Intros x y [H₁ [|] |].
    { Rewrite H₁. }
    { Rewrite H₁. }
    { Apply Conjunction.as_conditionₑ.
      Apply Set_.extensionality. }
  Defined.

  Theorem alternative_definition :
    𝒯 ⊢ ∀ x y, x = y ⇔ ∀ z, z ∈ x ⇔ z ∈ y.
  Proof.
    Intros x y.
    Rewrite Equality.alternative_definition₂.
    Rewrite <- Universality.split.
  Defined.
End Equality.