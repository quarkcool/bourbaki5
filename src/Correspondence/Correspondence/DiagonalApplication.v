Require Export
  Bourbaki.Correspondence.Correspondence.TermFunction.

Section DiagonalApplication.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall X, set_by_replacement (fun x => ❨x, x❩) X ⊢⊂ X × X.
  Proof.
    Change (forall X, ⊢ ∀ z, _).
    Rewrite MembershipEquivalenceProof.proof at 1.
    Intros X z [x H₁].
    Rewrite H₁.
    Apply CoupleMembershipEquivalenceProof.proof.
    Intros [|];
      Assumption.
  Qed.

  (* application diagonale de X *)
  Definition diagonal_application X : X → X × X := x ∈ X ↦ ❨x, x❩ ∈ X × X.
End DiagonalApplication.