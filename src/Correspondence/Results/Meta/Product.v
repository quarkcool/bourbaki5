Require Export
  Bourbaki.Set.CoupleMembershipEquivalenceProof
  Bourbaki.Set.Results.All.

Section Product.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall X Y,
      CoupleMembershipEquivalenceProof (X × Y) (fun x y => x ∈ X ∧ y ∈ Y).
  Proof.
    Intros X Y x y.
    Rewrite MembershipEquivalenceProof.proof;
      Change (⊢ (∃ x' y', _) ⇔ _).
    Apply Existence.of_equal_coupleₑ₂.
  Qed.
End Product.