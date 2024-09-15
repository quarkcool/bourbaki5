Require Export
  Bourbaki.Correspondence.Results.Meta.GraphProjections.

Section EmptyGraph.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    IsGraph ∅.
  Proof.
    Apply EmptySet.typical_universality.
  Qed.

  Theorem first_projectionₑ :
    ⊢ pr₁⟨∅⟩ = ∅.
  Proof.
    Apply EmptySet.as_equalₑ;
      Change (⊢ ∀ x, ¬_).
    Rewrite MembershipEquivalenceProof.proof.
    Intros x [y contra₁].
    Apply EmptySet.emptiness;
    Assumption.
  Qed.

  Theorem second_projectionₑ :
    ⊢ pr₂⟨∅⟩ = ∅.
  Proof.
    Apply EmptySet.as_equalₑ;
      Change (⊢ ∀ y, ¬_).
    Rewrite MembershipEquivalenceProof.proof.
    Intros y [x contra₁].
    Apply EmptySet.emptiness;
    Assumption.
  Qed.
End EmptyGraph.