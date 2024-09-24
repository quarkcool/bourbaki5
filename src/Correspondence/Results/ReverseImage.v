Require Export
  Bourbaki.Correspondence.Relation.Surjectivity
  Bourbaki.Correspondence.Results.Image
  Bourbaki.Correspondence.Results.Injectivity
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

  #[export]
  Instance :
    forall {X Y₁ Y₂} (f : X → Y₁) `(!Y₂ ⊢⊂ Y₁),
      MembershipEquivalenceProof f⁻¹⟨Y₂⟩ (fun x => x ∈ X ∧ f x ∈ Y₂)
  | 0.
  Proof.
    Intros X Y₁ Y₂ f H₁ x.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite <- (fun _ => Conjunction.commutativity (_ = _)).
    Rewrite TypicalExistence.of_equalₑ.
    Apply Conjunction.commutativity.
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

  (* Rem_E_II_3__2_i *)
  Theorem of_image_as_superset_when_functionₑ {X₁ Y} (f : X₁ → Y) :
    ⊢ ∀ X₂, X₂ ⊂ f⁻¹⟨f⟨X₂⟩⟩ ⇔ X₂ ⊂ X₁.
  Proof.
    Intros X₂.
    Rewrite ReverseImage.of_image_as_supersetₑ.
    Rewrite Application.first_projectionₑ.
  Qed.

  (* Rem_E_II_3__2_iv *)
  Theorem of_imageₑ {X₁ Y} (f : X₁ → Y) :
    ⊢ is_injective f ⇒ ∀ X₂, X₂ ⊂ X₁ ⇒ f⁻¹⟨f⟨X₂⟩⟩ = X₂.
  Proof.
    Rewrite Set_.equalityₑ.
    Intros H₁ X₂ H₂ x.
    do 2 (unfold typical_existence; Rewrite MembershipEquivalenceProof.proof);
      Change (⊢ (∃ y, (∃ x' ⟨_⟩, _) ∧ _) ⇔ _).
    Rewrite <- TypicalExistence.conjunct_extraction_right;
      Change (⊢ (∃ y, ∃ x' ⟨_⟩, _) ⇔ _).
    Rewrite <- TypicalExistence.switch_with_atypical;
      Change (⊢ (∃ x' ⟨_⟩, ∃ y, _) ⇔ _).
    Rewrite Existence.of_equalₑ.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite (_ : ∃ x' ⟨_⟩, _ ⊢⇔ ∃ x' ⟨∈ X₂⟩, x' = x ∧ x ∈ X₁ ∧ f x' = f x).
    { Apply TypicalExistence.conditional_rewriting.
      Intros x' H₃.
      Rewrite Conjunction.associativity.
      Rewrite <- (Conjunction.commutativity (_ ∈ _)).
      Rewrite <- Conjunction.associativity.
      Apply Conjunction.conditional_rewriting_right.
      Intros H₄.
      Rewrite (Conjunction.operand_removal_left (_ = _)).
      Apply Injectivity.alternative_definition;
        plus [() | Apply H₂];
        Assumption. }
    { Rewrite TypicalExistence.of_equalₑ.
      Apply Conjunction.operand_removal_right.
      Intros H₃ [|].
      { Apply H₂.
        Assumption. }
      { Reflexivity. } }
  Qed.
End ReverseImage.

Module Image.
  Section Image.
    Context `{Set_.Theory}.

    (* Rem_E_II_3__2_ii *)
    Theorem of_reverse_image_as_subset {X Y₁} (f : X → Y₁) :
      ⊢ ∀ Y₂, Y₂ ⊂ Y₁ ⇒ f⟨f⁻¹⟨Y₂⟩⟩ ⊂ Y₂.
    Proof.
      Change (⊢ ∀ Y₂, _ ⇒ ∀ y, _).
      do 2 (unfold typical_existence; Rewrite MembershipEquivalenceProof.proof);
        Change (⊢ ∀ Y₂, _ ⇒ ∀ y, (∃ x, (∃ y' ⟨_⟩, _) ∧ _) ⇒ _).
      Rewrite CoupleMembershipEquivalenceProof.proof.
      Intros Y₂ H₁ y [x [[y' H₂] H₃]].
      Rewrite H₃.
      Rewrite <- H₂.
      Assumption.
    Qed.

    (* Rem_E_II_3__2_iii *)
    Theorem of_reverse_imageₑ {X Y₁} (f : X → Y₁) :
      ⊢ is_surjective f ⇒ ∀ Y₂, Y₂ ⊂ Y₁ ⇒ f⟨f⁻¹⟨Y₂⟩⟩ = Y₂.
    Proof.
      Rewrite Set_.equalityₑ at 2.
      Intros H₁ Y₂ H₂ y.
      do 2 (unfold typical_existence; Rewrite MembershipEquivalenceProof.proof);
        Change (⊢ (∃ x, _) ⇔ _).
      Rewrite CoupleMembershipEquivalenceProof.proof.
      Rewrite Conjunction.associativity.
      Rewrite <- (
        fun _ => Equality.as_conjunct_rightₑ _ _ (fun x => (_ ∧ x ∈ _) ∧ _)
      ).
      Rewrite <- (Conjunction.commutativity (_ ∈ _)).
      Rewrite <- (Conjunction.associativity (_ ∈ _)).
      Rewrite Conjunction.idempotenceₑ.
      Rewrite <- Conjunction.associativity.
      Rewrite Existence.conjunct_extraction_left.
      Apply Conjunction.operand_removal_right.
      Intros H₃.
      Apply (MembershipEquivalenceProof.proof f⟨X⟩).
      Rewrite H₁.
      Apply H₂.
      Assumption.
    Qed.
  End Image.
End Image.