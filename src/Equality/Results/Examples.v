Require Export
  Bourbaki.Equality.Results.All
  Bourbaki.Equality.Results.FunctionalRelation.

Import Proof.TheoryHidingNotation.

Section Examples.
  Context `(EqualitarianTheory).

  Example TH3 x y z :
    𝒯 ⊢ x = y ∧ y = z ⇒ x = z.
  Proof.
    Rewrite Conjunction.as_conditionₑ.
    Apply Equality.transitivity.
  Defined.

  Example C44 T U V :
    𝒯 ⊢ T = U ⇒ V T = V U.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C47 {𝐑} `(!FunctionalRelation 𝒯 𝐑) 𝐒 :
    𝒯 ⊢ 𝐒 (τ x, 𝐑 x) ⇔ ∃ x ⟨ 𝐑 ⟩, 𝐒 x.
  Proof.
    unfold TypicalExistence.typical_existence.
    Rewrite (FunctionalRelation.unique_value (𝐑 := 𝐑)) at 2.
    Rewrite Existence.of_equal.
  Defined.
End Examples.