Require Export
  Bourbaki.Correspondence.Results.Coincidence
  Bourbaki.Correspondence.Results.Graph
  Bourbaki.Correspondence.Results.Value.

Section Application.
  Context `{Set_.Theory}.

  Theorem first_projectionₑ {F X Y} `(!IsFunction F X Y) :
    ⊢ pr₁⟨F⟩ = X.
  Proof.
    Symmetry.
    Apply FunctionEssence.function_essence.
  Qed.

  #[export]
  Instance :
    forall {X Y} (f : X → Y),
      CoupleMembershipEquivalenceProof f (fun x y => x ∈ X ∧ y = f x).
  Proof.
    Intros X Y f x y [H₁ | [H₁ H₂]].
    { Apply Conjunction.operand_removal_right.
      { Intros H₂.
        Apply Value.as_equalₑ.
        Assumption. }
      { Rewrite <- (Application.first_projectionₑ (F := f)) at 2.
        Apply MembershipEquivalenceProof.proof.
        Assumption. } }
    { Rewrite H₂.
      Apply Value.value_essence. }
  Qed.

  #[export]
  Instance :
    forall {F X Y} `(!IsFunction F X Y), IsCorrespondence F X Y.
  Proof.
    Intros F X Y H₁.
    Apply FunctionEssence.function_essence.
  Qed.

  Theorem inclusionₑ {X₁ Y₁ X₂ Y₂} (f : X₁ → Y₁) (g : X₂ → Y₂) :
    ⊢ f ⊂ g ⇔ X₁ ⊂ X₂ ∧ coincidence f g X₁.
  Proof.
    Intros [H₁ | [H₁ H₂]].
    { Apply Conjunction.operand_removal_right.
      { Intros H₂ [[|] | x H₃].
        { Reflexivity. }
        { Assumption. }
        { assert (H₄ : ⊢ x ∈ X₂). { Apply H₂. Assumption. }
          Apply Value.as_equalₑ.
          Apply H₁.
          Apply Value.value_essence. } }
      { Rewrite <- (Application.first_projectionₑ (F := f)).
        Rewrite H₁.
        Apply (Correspondence.first_projection_subset_essence (G := g)). } }
    { Apply Graph.inclusionₑ.
      Rewrite CoupleMembershipEquivalenceProof.proof.
      Rewrite <- H₁ at 1.
      Intros x y H₃ [|].
      { Assumption. }
      { Rewrite <- H₂;
          Assumption. } }
  Qed.

  Theorem equalityₑ {X₁ Y₁ X₂ Y₂} (f : X₁ → Y₁) (g : X₂ → Y₂) :
    ⊢ f = g ⇔ X₁ = X₂ ∧ coincidence f g X₁.
  Proof.
    Rewrite (⇑Set_.equalityₑ₂ f).
    do 2 (Rewrite Application.inclusionₑ).
    Rewrite <- (Conjunction.associativity (_ ⊂ _)).
    Rewrite (Conjunction.commutativity (coincidence _ _ _)).
    Rewrite <- (Conjunction.associativity (_ ⊂ _)).
    Rewrite (Conjunction.associativity (_ ⊂ _)).
    Rewrite <- Set_.equalityₑ₂.
    Apply Conjunction.conditional_rewriting_right.
    Intros H₁.
    Rewrite Coincidence.commutativity.
    Rewrite <- H₁ at 2.
    Apply Conjunction.idempotenceₑ.
  Qed.

  Theorem equality_when_same_domainₑ {X Y₁ Y₂} (f : X → Y₁) (g : X → Y₂) :
    ⊢ f = g ⇔ ∀ x ⟨∈ X⟩, f x = g x.
  Proof.
    Rewrite Application.equalityₑ.
    Rewrite (Conjunction.operand_removal_left _ (_ = _)).
    { Apply Conjunction.operand_removal_left.
      Intros _ [|];
        Reflexivity. }
    { Apply Equality.reflexivity. }
  Qed.
End Application.