Require Export
  Bourbaki.Correspondence.Results.Cut.

Section Graph.
  Context `{Set_.Theory}.

  Theorem equalityₑ (G₁ G₂ : Graph) :
    ⊢ G₁ = G₂ ⇔ ∀ x y, ❨x, y❩ ∈ G₁ ⇔ ❨x, y❩ ∈ G₂.
  Proof.
    Rewrite Set_.equalityₑ₂.
    Rewrite Graph.inclusionₑ.
    do 2 (Rewrite <- Universality.split).
  Qed.

  Theorem inclusionₑ₂ (G₁ G₂ : Graph) :
    ⊢ G₁ ⊂ G₂ ⇔ ∀ x, cut G₁ x ⊂ cut G₂ x.
  Proof.
    Change (⊢ _ ⇔ ∀ x y, _).
    Rewrite MembershipEquivalenceProof.proof.
    Apply Graph.inclusionₑ.
  Qed.
End Graph.