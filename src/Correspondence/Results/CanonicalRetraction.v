Require Export
  Bourbaki.Correspondence.Correspondence.CanonicalRetraction.

Section CanonicalRetraction.
  Context `{Set_.Theory}.

  (* Pr_E_II_3__8_iv *)
  Theorem retraction_essence
    {X Y} (f : X → Y) `(!Inhabited (Element X)) `(!IsInjective f) :
      ⊢ is_retraction (canonical_retraction f) f.
  Proof.
    Apply Application.equality_when_same_domainₑ.
    Intros x H₁.
    Rewrite ValueEqualityProof.proof.
    Symmetry.
    assert (H₂ : ⊢ f x ∈ Y). {
      Apply (Correspondence.second_projection_subset_essence (G := f)).
      Apply Value.element_essence.
    }
    Apply Value.as_equalₑ.
    Apply CoupleMembershipEquivalenceProof.proof; Change (⊢ _ ∨ _).
    Apply Logic.disjunction_introduction_left.
    Intros [|].
    { Assumption. }
    { Reflexivity. }
  Qed.
End CanonicalRetraction.