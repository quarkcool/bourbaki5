Require Export
  Bourbaki.Correspondence.Results.Meta.GraphProjections.

Section GraphProjections.
  Context `{Set_.Theory}.

  Theorem alternative_definition₁ (G : Graph) :
    ⊢ pr₁⟨G⟩ = set_by_replacement pr₁ G.
  Proof.
    Apply Set_.equalityₑ.
    Rewrite MembershipEquivalenceProof.proof at 1.
    Apply GraphProjections.membership_equivalenceₑ₁.
  Qed.

  Theorem alternative_definition₂ (G : Graph) :
    ⊢ pr₂⟨G⟩ = set_by_replacement pr₂ G.
  Proof.
    Apply Set_.equalityₑ.
    Rewrite MembershipEquivalenceProof.proof at 1;
      Change (⊢ ∀ y, (∃ x, _) ⇔ _).
    Apply GraphProjections.membership_equivalenceₑ₂.
  Qed.
End GraphProjections.