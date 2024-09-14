Require Export
  Bourbaki.Equality.Results.Meta.Truth
  Bourbaki.Quantification.Results.Meta.Universality
  Bourbaki.Set.CoupleMembershipEquivalenceProof.

Section CoupleMembershipEquivalenceProof.
  Context `{Quantification.Theory, !Equality.Syntax, !Set_.Syntax}.

  #[export]
  Instance :
    forall X, CoupleMembershipEquivalenceProof X (fun x y => ❨x, y❩ ∈ X) | 100.
  Proof.
    Intros X x y.
    Reflexivity.
  Qed.
End CoupleMembershipEquivalenceProof.