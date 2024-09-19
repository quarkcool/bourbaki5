Require Export
  Bourbaki.Correspondence.Results.Meta.GraphComposite
  Bourbaki.Correspondence.Results.ReverseGraph.

Section GraphComposite.
  Context `{Set_.Theory}.

  (* Pr_E_II_3__4 *)
  Theorem associativity G₁ G₂ G₃ :
    ⊢ G₁ ∘ G₂ ∘ G₃ = (G₁ ∘ G₂) ∘ G₃.
  Proof.
    Apply Graph.equalityₑ.
    Intros x z.
    do 2 (Rewrite CoupleMembershipEquivalenceProof.proof);
      Change (⊢ (∃ y₂, (∃ y₁, _) ∧ _) ⇔ ∃ y₁, _ ∧ ∃ y₂, _).
    Rewrite <- Existence.conjunct_extraction_right;
      Change (⊢ (∃ y₂ y₁, _) ⇔ _).
    Rewrite <- Conjunction.associativity.
    Rewrite Existence.switch;
      Change (⊢ (∃ y₁ y₂, _) ⇔ _).
    Rewrite Existence.conjunct_extraction_left.
  Qed.

  Theorem first_projectionₑ G₁ G₂ :
    ⊢ pr₁⟨G₁ ∘ G₂⟩ = G₂⁻¹⟨pr₁⟨G₁⟩⟩.
  Proof.
    Apply Set_.equalityₑ.
    Intros x.
    do 2 (unfold typical_existence; Rewrite MembershipEquivalenceProof.proof);
      Change (⊢ (∃ z, _) ⇔ ∃ y, (∃ z, _) ∧ _).
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite (fun _ => Conjunction.commutativity (_ ∈ _)).
    Rewrite Existence.switch;
      Change (⊢ (∃ y z, _) ⇔ _).
    Rewrite Existence.conjunct_extraction_right.
  Qed.

  (* Pr_E_II_3__5 *)
  Theorem imageₑ G₁ G₂ :
    ⊢ ∀ X, (G₁ ∘ G₂)⟨X⟩ = G₁⟨G₂⟨X⟩⟩.
  Proof.
    Rewrite Set_.equalityₑ.
    Intros X z.
    do 2 (unfold typical_existence; Rewrite MembershipEquivalenceProof.proof);
      Change (⊢ _ ⇔ ∃ y, _).
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite TypicalExistence.switch_with_atypical.
    Rewrite TypicalExistence.conjunct_extraction_right.
  Qed.

  (* Pr_E_II_3__3 *)
  Theorem reverseₑ G₁ G₂ :
    ⊢ (G₁ ∘ G₂)⁻¹ = G₂⁻¹ ∘ G₁⁻¹.
  Proof.
    Apply Graph.equalityₑ.
    Intros z x.
    do 2 (Rewrite CoupleMembershipEquivalenceProof.proof).
    Rewrite (fun _ => Conjunction.commutativity (_ ∈ _)).
  Qed.

  Theorem second_projectionₑ G₁ G₂ :
    ⊢ pr₂⟨G₁ ∘ G₂⟩ = G₁⟨pr₂⟨G₂⟩⟩.
  Proof.
    Apply Set_.equalityₑ.
    Intros z.
    do 2 (unfold typical_existence; Rewrite MembershipEquivalenceProof.proof);
      Change (⊢ _ ⇔ ∃ y, _).
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite Existence.switch.
    Rewrite Existence.conjunct_extraction_right.
  Qed.
End GraphComposite.