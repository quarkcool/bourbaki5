Require Export
  Bourbaki.Correspondence.Results.Application
  Bourbaki.Correspondence.Term.Correspondence.

Section Image.
  Context `{Set_.Theory}.

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

  #[export]
  Instance :
    forall {X Y} (f : X → Y), f⟨X⟩ ⊢⊂ Y.
  Proof.
    Intros X Y f.
    Rewrite Image.of_starting_set.
    Apply Correspondence.second_projection_subset_essence.
  Qed.

  #[export]
  Instance :
    forall {X₁ Y X₂} (f : X₁ → Y) `(!X₂ ⊢⊂ X₁),
      MembershipEquivalenceProof f⟨X₂⟩ (fun y => ∃ x ⟨∈ X₂⟩, y = f x)
  | 0.
  Proof.
    Intros X₁ Y X₂ f H₁ y.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Apply TypicalExistence.conditional_rewriting.
    Intros x H₂.
    Apply Conjunction.operand_removal_left.
    Apply H₁.
    Assumption.
  Qed.

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
End Image.