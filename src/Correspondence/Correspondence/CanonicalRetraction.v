Require Export
  Bourbaki.Correspondence.Results.Injectivity.

Section CanonicalRetraction.
  Context `{Set_.Theory}.
  Context {X Y} (f : X → Y) `(!Inhabited (Element X)).

  Let 𝐑 :=
  fun x y => (y ∈ X ∧ x = f y) ∨ x ∈ ∁ Y f⟨X⟩ ∧ y = (default : Element X).

  #[export]
  Instance :
    HasGraph 𝐑.
  Proof.
    unfold 𝐑.
    Rewrite MembershipEquivalenceProof.proof.
    Apply GraphPossession.from_container_set.
    Intros [x y [[H₂ H₃] | H₂]];
      Apply (CoupleMembershipEquivalenceProof.proof (Y × X));
      Intros [|].
      { Rewrite H₃.
        Apply (Correspondence.second_projection_subset_essence (G := f)).
        Apply Value.element_essence. }
      1-2: Assumption.
      { Rewrite H₂.
        Apply Element.membership. }
  Qed.

  Theorem first_projectionₑ :
    ⊢ pr₁⟨{❨x, y❩ | 𝐑 x y}⟩ = Y.
  Proof.
    unfold 𝐑.
    Apply Set_.equalityₑ.
    Intros x.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite Existence.split;
      Change (⊢ (∃ y, _) ∨ (∃ y, _) ⇔ _).
    Rewrite <- (
      MembershipEquivalenceProof.proof f⟨X⟩ (fun x => ∃ y ⟨∈ X⟩, x = f y)
    ).
    Rewrite (Conjunction.commutativity (_ ∈ _)).
    Rewrite Existence.of_equalₑ.
    Rewrite (MembershipEquivalenceProof.proof (∁ Y f⟨X⟩)).
    Rewrite <- (Conjunction.operand_removal_right (x ∈ f⟨X⟩) (x ∈ Y)).
    { Rewrite <- Conjunction.distributivity_over_disjunction_right.
      Apply Conjunction.operand_removal_left.
      Apply Logic.excluded_middle. }
    { Rewrite Image.of_starting_set.
      Apply Correspondence.second_projection_subset_essence. }
  Qed.

  Theorem second_projection_subset_essence :
    ⊢ pr₂⟨{❨x, y❩ | 𝐑 x y}⟩ ⊂ X.
  Proof.
    unfold 𝐑.
    Intros y.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite MembershipEquivalenceProof.proof.
    Intros [x [H₁ | H₁]].
    { Assumption. }
    { Rewrite H₁.
      Apply Element.membership. }
  Qed.

  #[export]
  Instance :
    IsCorrespondence {❨x, y❩ | 𝐑 x y} Y X.
  Proof.
    Intros [|].
    { Rewrite CanonicalRetraction.first_projectionₑ. }
    { Apply CanonicalRetraction.second_projection_subset_essence. }
  Qed.

  #[export]
  Instance :
    IsInjective f -> IsFunction {❨x, y❩ | 𝐑 x y} Y X.
  Proof.
    unfold 𝐑.
    Intros H₁ [| [x y₁ y₂ |]].
    { Rewrite CoupleMembershipEquivalenceProof.proof.
      Rewrite MembershipEquivalenceProof.proof.
      Intros [H₂ | H₂] [H₃ | H₃].
      { Apply Injectivity.alternative_definition.
        { Apply Injectivity.injectivity. }
        1-2: Assumption.
        { Rewrite <- H₂.
          Rewrite <- H₃. } }
      { Exfalso.
        Apply H₃; Change (⊢ _ ∈ _).
        Apply MembershipEquivalenceProof.proof.
        Assumption. }
      { Exfalso.
        Apply H₂; Change (⊢ _ ∈ _).
        Apply MembershipEquivalenceProof.proof.
        Assumption. }
      { Rewrite H₂.
        Rewrite H₃. } }
    { fold 𝐑.
      Rewrite CanonicalRetraction.first_projectionₑ. }
  Qed.

  Definition canonical_retraction `(!IsInjective f) :
    Y → X :=
  {❨x, y❩ | 𝐑 x y}.
End CanonicalRetraction.

Arguments canonical_retraction {_ _ _ _ _ _ _ _ _ _} _ {_ _}.