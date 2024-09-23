Require Export
  Bourbaki.Correspondence.Correspondence.TermFunction.

Section IdenticalApplication.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall X, set_by_replacement (fun x => x) X ⊢⊂ X.
  Proof.
    Intros X y.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite Equality.commutativity.
    Apply Existence.of_equalₑ.
  Qed.

  (* application identique *)
  Definition identical_application X : X → X := x ∈ X ↦ x ∈ X.
End IdenticalApplication.

Notation Id := identical_application.