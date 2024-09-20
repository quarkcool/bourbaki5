Require Export
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
End Application.