Require Export
  Bourbaki.Correspondence.Results.Correspondence
  Bourbaki.Correspondence.Results.Meta.Image
  Bourbaki.Correspondence.Term.Correspondence.

Section Image.
  Context `{Set_.Theory}.

  Theorem non_emptinessₑ (G : Graph) :
    ⊢ ∀ X, X ⊂ pr₁⟨G⟩ ⇒ (is_non_empty G⟨X⟩ ⇔ is_non_empty X).
  Proof.
    Intros X.
    Change (⊢ (∀ x, _) ⇒ ((∃ y, _) ⇔ _)).
    Rewrite MembershipEquivalenceProof.proof.
    Intros H₁.
    Rewrite <- TypicalExistence.switch_with_atypical;
      Change (⊢ (∃ x, _ ∧ ∃ y, _) ⇔ _).
    Rewrite (fun _ => Conjunction.operand_removal_right (_ ∈ _)).
    Assumption.
  Qed.

  Theorem of_empty_set G :
    ⊢ G⟨∅⟩ = ∅.
  Proof.
    Apply EmptySet.as_equalₑ;
      Change (⊢ ∀ y, ¬_).
    Rewrite MembershipEquivalenceProof.proof.
    Intros y [x contra₁].
    Apply EmptySet.emptiness;
    Assumption.
  Qed.

  Theorem of_first_projection G :
    ⊢ G⟨pr₁⟨G⟩⟩ = pr₂⟨G⟩.
  Proof.
    Rewrite Set_.equalityₑ.
    Intros y.
    do 2 (unfold typical_existence; Rewrite MembershipEquivalenceProof.proof);
      Change (⊢ (∃ x, (∃ y', _) ∧ _) ⇔ _).
    Rewrite (fun _ => Conjunction.operand_removal_left _ (∃ y', _)).
    Intros H₁.
    Assumption.
  Qed.

  Theorem subset_of_second_projection_essence G :
    ⊢ ∀ X, G⟨X⟩ ⊂ pr₂⟨G⟩.
  Proof.
    Intros X y.
    Rewrite MembershipEquivalenceProof.proof.
    Intros [x H₂].
    Assumption.
  Qed.

  (* Corr_E_II_3__1 *)
  Theorem of_set_bigger_than_first_projection (G : Graph) :
    ⊢ ∀ X, pr₁⟨G⟩ ⊂ X ⇒ G⟨X⟩ = pr₂⟨G⟩.
  Proof.
    Intros X H₁.
    Apply Set_.equalityₑ₂.
    Apply Conjunction.operand_removal_left.
    { Apply Image.subset_of_second_projection_essence. }
    { Rewrite <- H₁.
      Rewrite Image.of_first_projection. }
  Qed.

  Theorem of_starting_set {X Y} (Γ : Correspondence X Y) :
    ⊢ Γ⟨X⟩ = pr₂⟨Γ⟩.
  Proof.
    Apply Image.of_set_bigger_than_first_projection.
    Apply Correspondence.first_projection_subset_essence.
  Qed.
End Image.