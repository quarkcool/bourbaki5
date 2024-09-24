Require Export
  Bourbaki.Correspondence.Correspondence.ReverseApplication.

Section ReverseApplication.
  Context `{Set_.Theory}.

  Theorem value_passed_to_reversed_application
    {X Y} (f : X → Y) `(!IsBijective f) :
      ⊢ ∀ y ⟨∈ Y⟩, f ((f⁻¹ : _ → _) y) = y.
  Proof.
    Intros y H₁.
    Symmetry.
    assert (H₄ : ⊢ (f⁻¹ : Y → _) y ∈ X). {
      Apply (Correspondence.second_projection_subset_essence (G := f⁻¹)).
      Apply Value.element_essence.
    }
    Apply Value.as_equalₑ.
    Apply (CoupleMembershipEquivalenceProof.proof f⁻¹ (fun x y => ❨y, x❩ ∈ f)).
    Apply Value.value_essence.
  Qed.

  #[export]
  Instance :
    forall {X Y} (f : X → Y) `(!IsBijective f), IsBijective f⁻¹.
  Proof.
    Intros X Y f H₁ [|].
    { Apply Injectivity.alternative_definition.
      Intros y₁ H₂ y₂ H₃ H₄.
      Rewrite <- ReverseApplication.value_passed_to_reversed_application.
      { Rewrite H₄. }
      all: Assumption. }
    { Change (⊢ _ = _).
      Rewrite Image.of_starting_set.
      Rewrite ReverseGraph.second_projectionₑ.
      Apply Application.first_projectionₑ. }
  Qed.
End ReverseApplication.