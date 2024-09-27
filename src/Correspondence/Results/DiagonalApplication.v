Require Export
  Bourbaki.Correspondence.Correspondence.DiagonalApplication
  Bourbaki.Correspondence.Results.Injectivity.

Section DiagonalApplication.
  Context `{Set_.Theory}.

  Theorem injectivity X :
    ⊢ is_injective (diagonal_application X).
  Proof.
    Apply Injectivity.alternative_definition.
    Intros x₁ H₁ x₂ H₂.
    Rewrite ValueEqualityProof.proof.
    Rewrite Couple.equalityₑ.
    Apply Conjunction.idempotenceₑ.
  Qed.
End DiagonalApplication.