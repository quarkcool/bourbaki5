Require Export
  Bourbaki.Correspondence.Results.ReverseGraph.

Section ReverseImage.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall G Y,
      MembershipEquivalenceProof G⁻¹⟨Y⟩ (fun x => ∃ y ⟨∈ Y⟩, ❨x, y❩ ∈ G)
  | 0.
  Proof.
    Intros G Y x.
    Rewrite MembershipEquivalenceProof.proof;
      Change (⊢ (∃ y, _) ⇔ _).
    Rewrite CoupleMembershipEquivalenceProof.proof.
  Qed.
End ReverseImage.