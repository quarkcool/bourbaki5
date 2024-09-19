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

  Theorem of_image_as_supersetₑ G :
    ⊢ ∀ X, X ⊂ G⁻¹⟨G⟨X⟩⟩ ⇔ X ⊂ pr₁⟨G⟩.
  Proof.
    Intros X.
    Change (⊢ (∀ x ⟨_⟩, _) ⇔ ∀ x ⟨_⟩, _).
    do 2 (unfold typical_existence; Rewrite MembershipEquivalenceProof.proof);
      Change (⊢ (∀ x ⟨_⟩, ∃ y, (∃ x', _) ∧ _) ⇔ _).
    Apply TypicalUniversality.conditional_rewriting.
    Intros x H₁.
    Rewrite (fun _ => Conjunction.operand_removal_left (_ ∈ _)).
    Intros H₂ [[|]];
      Assumption.
  Qed.
End ReverseImage.