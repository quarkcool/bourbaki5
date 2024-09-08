Require Export
  Bourbaki.Set.Results.MembershipEquivalenceProof
  Bourbaki.Set.Results.Meta.CollectivizingSubset.

Section CollectivizingSubset.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall X 𝐑, {x ∈ X | 𝐑 x} ⊢⊂ X.
  Proof.
    Intros X 𝐑 x.
    Rewrite MembershipEquivalenceProof.proof.
    Apply Conjunction.elimination_right.
  Qed.
End CollectivizingSubset.