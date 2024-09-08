Require Export
  Bourbaki.Equality.Results.Meta.Truth
  Bourbaki.Quantification.Results.Meta.Universality
  Bourbaki.Set.MembershipEquivalenceProof.

Section MembershipEquivalenceProof.
  Context `{Quantification.Theory, !Equality.Syntax, !Set_.Syntax}.

  #[export]
  Instance :
    forall X, MembershipEquivalenceProof X (∈ X) | 100.
  Proof.
    Intros X x.
    Reflexivity.
  Qed.
End MembershipEquivalenceProof.