Require Export
  Bourbaki.Correspondence.Correspondence.TermFunction
  Bourbaki.Correspondence.Results.Application.

Section Restriction.
  Context `{Set_.Theory}.
  Context {X₁ Y X₂} (f : X₁ → Y) `(!X₂ ⊢⊂ X₁).

  #[export]
  Instance :
    set_by_replacement (value f) X₂ ⊢⊂ Y.
  Proof.
    Change (⊢ ∀ y, _).
    Rewrite MembershipEquivalenceProof.proof.
    Intros y [x H₁].
    Rewrite H₁.
    Apply (Correspondence.second_projection_subset_essence (G := f)).
    assert (H₂ : ⊢ x ∈ X₁). {
      Apply (InclusionProof.proof (x := X₂)).
      Assumption.
    }
    Apply Value.element_essence.
  Qed.

  (* restriction de f à X₂ *)
  Definition restriction : X₂ → Y := x ∈ X₂ ↦ f x ∈ Y.
End Restriction.

Notation "f ∥ X" := (restriction (X₂ := X) f _) : bourbaki_scope.