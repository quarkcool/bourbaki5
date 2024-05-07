Require Export
  Bourbaki.Quantification.Relation.TypicalExistence
  Bourbaki.Quantification.Relation.TypicalUniversality
  Bourbaki.Quantification.Results.Meta.Universality.

Import Proof.TheoryHidingNotation.

Section Examples.
  Context `(QuantifiedTheory).

  Example C36 {𝐀 𝐑} :
    (forall x, 𝐀 x ∷ 𝒯 ⊢ 𝐑 x) -> 𝒯 ⊢ ∀ x ⟨ 𝐀 ⟩, 𝐑 x.
  Proof.
    Intros H₁ x.
    Apply Proof.deduction.
    Assumption.
  Defined.

  Example C37 {𝐑 𝐀} :
    (forall x, Contradictory (¬𝐑 x ∷ 𝐀 x ∷ 𝒯)) -> 𝒯 ⊢ ∀ x ⟨ 𝐀 ⟩, 𝐑 x.
  Proof.
    Intros H₁ x.
    destruct (H₁ x) as [𝐁 [H₂ H₃]].
    Intros H₄ ?contra₁;
      Assumption.
  Defined.
End Examples.