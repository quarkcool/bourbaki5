Require Export
  Bourbaki.Correspondence.Correspondence.IdenticalCorrespondence
  Bourbaki.Correspondence.Term.Application.

Section IdenticalApplication.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall X, IsFunction (Δ X) X X.
  Proof.
    Intros X [| [x y₁ y₂ |]].
    { Rewrite CoupleMembershipEquivalenceProof.proof.
      Intros H₁ H₂.
      Rewrite H₁.
      Rewrite H₂. }
    { Rewrite Diagonal.first_projectionₑ. }
  Qed.

  (* application identique *)
  Definition identical_application X : X → X := Δ X.
End IdenticalApplication.