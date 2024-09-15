Require Export
  Bourbaki.Correspondence.Results.Meta.Image
  Bourbaki.Correspondence.Term.Cut.

Section Cut.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall G x, MembershipEquivalenceProof (cut G x) (fun y => ❨x, y❩ ∈ G)
  | 0.
  Proof.
    Intros G x y.
    Rewrite MembershipEquivalenceProof.proof.
    Apply Singleton.typical_existenceₑ.
  Qed.
End Cut.