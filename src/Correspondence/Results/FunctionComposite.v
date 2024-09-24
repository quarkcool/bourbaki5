Require Export
  Bourbaki.Correspondence.Correspondence.FunctionComposite
  Bourbaki.Correspondence.Results.TermFunction.

Section FunctionComposite.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall {Y Z X} (g : Y → Z) (f : X → Y),
      ValueEqualityProof (function_composite g f) (fun x => g (f x)).
  Proof.
    Intros Y Z X g f x.
    Symmetry.
    Apply Value.as_equalₑ.
    Apply CoupleMembershipEquivalenceProof.proof; Change (⊢ ∃ y, _).
    Rewrite <- Value.as_equalₑ at 1.
    Apply Existence.of_equalₑ.
    assert (H₂ : ⊢ f x ∈ Y). {
      Apply (Correspondence.second_projection_subset_essence (G := f)).
      Apply Value.element_essence.
    }
    Apply Value.value_essence.
  Qed.

  Theorem alternative_definition {Y Z X} (g : Y → Z) (f : X → Y) :
    ⊢ function_composite g f = (x ∈ X ↦ g (f x)).
  Proof.
    Apply Application.equality_when_same_domainₑ.
    Intros x H₁.
    Rewrite ValueEqualityProof.proof.
  Qed.
End FunctionComposite.