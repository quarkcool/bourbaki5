Require Export
  Bourbaki.Correspondence.Correspondence.TermFunction
  Bourbaki.Correspondence.Results.Application
  Bourbaki.Correspondence.Results.ValueEqualityProof.

Section TermFunction.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall {X Y} (f : X → Y), set_by_replacement (value f) X ⊢⊂ Y.
  Proof.
    Change (forall X Y f, ⊢ ∀ y, _).
    Rewrite MembershipEquivalenceProof.proof.
    Intros X Y f y [x [H₁ H₂]].
    Rewrite H₁.
    Apply (Correspondence.second_projection_subset_essence (G := f)).
    Apply Value.element_essence.
  Qed.

  (* C54_v *)
  #[export]
  Instance :
    forall {X Y} 𝐓 `(!set_by_replacement 𝐓 X ⊢⊂ Y),
      ValueEqualityProof (x ∈ X ↦ 𝐓 x ∈ Y) 𝐓.
  Proof.
    Intros X Y 𝐓 H₁ x.
    Symmetry.
    Apply Value.as_equalₑ.
    Apply CoupleMembershipEquivalenceProof.proof; Change (⊢ _ ∧ _ = 𝐓 _).
    Intros [|].
    { Apply Element.membership. }
    { Reflexivity. }
  Qed.

  Theorem over_values {X Y} (f : X → Y) :
    ⊢ (x ∈ X ↦ f x ∈ Y) = f.
  Proof.
    Apply Application.equality_when_same_domainₑ.
    Intros x H₁.
    Rewrite ValueEqualityProof.proof.
  Qed.
End TermFunction.