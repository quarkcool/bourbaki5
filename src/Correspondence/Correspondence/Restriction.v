Require Export
  Bourbaki.Correspondence.Results.Application
  Bourbaki.Correspondence.Results.RelationSubgraph.

Section Restriction.
  Context `{Set_.Theory}.
  Context {X₁ Y X₂} (f : X₁ → Y) `(!X₂ ⊢⊂ X₁).

  Theorem first_projectionₑ :
    ⊢ pr₁⟨{❨x, _❩ ∈ f | x ∈ X₂}⟩ = X₂.
  Proof.
    Apply Set_.equalityₑ.
    Intros x.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite Existence.conjunct_extraction_left;
      Change (⊢ _ ∧ (∃ y, _) ⇔ _).
    Rewrite <- (
      MembershipEquivalenceProof.proof pr₁⟨f⟩ (fun x => ∃ y, ❨x, y❩ ∈ f)
    ).
    Rewrite Application.first_projectionₑ.
    Apply Conjunction.operand_removal_right.
    Assumption.
  Qed.

  Theorem second_projection_subset_essence :
    ⊢ pr₂⟨{❨x, _❩ ∈ f | x ∈ X₂}⟩ ⊂ Y.
  Proof.
    Rewrite RelationSubgraph.subset_essence.
    Apply (Correspondence.second_projection_subset_essence (G := f)).
  Qed.

  #[export]
  Instance :
    IsCorrespondence {❨x, _❩ ∈ f | x ∈ X₂} X₂ Y.
  Proof.
    Intros [|].
    { Rewrite Restriction.first_projectionₑ. }
    { Apply Restriction.second_projection_subset_essence. }
  Qed.

  #[export]
  Instance :
    IsFunction {❨x, _❩ ∈ f | x ∈ X₂} X₂ Y.
  Proof.
    Intros [| [x y₁ y₂ |]].
    { do 2 (Rewrite CoupleMembershipEquivalenceProof.proof).
      Intros H₁ H₂.
      Rewrite H₁.
      Rewrite H₂. }
    { Rewrite Restriction.first_projectionₑ. }
  Qed.

  (* restriction de f à X₁ *)
  Definition restriction : X₂ → Y := {❨x, _❩ ∈ f | x ∈ X₂}.
End Restriction.

Notation "f ∥ X" := (restriction (X₂ := X) f _) : bourbaki_scope.