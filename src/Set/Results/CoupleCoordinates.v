Require Export
  Bourbaki.Set.Results.Couple
  Bourbaki.Set.Term.CoupleCoordinates.

Section CoupleCoordinates.
  Context `{Set_.Theory}.

  #[export]
  Instance functional_essence₁ :
    forall z, (⊢ is_couple z) -> IsFunctional (fun x => ∃ y, z = ❨x, y❩).
  Proof.
    Intros z H₁ [| x₁ x₂ [y₁ H₂] [y₂ H₃]].
    { Assumption. }
    { Apply Conjunction.elimination_left.
      Apply Couple.equalityₑ.
      Rewrite <- H₂.
      Rewrite <- H₃. }
  Qed.

  #[export]
  Instance functional_essence₂ :
    forall z, (⊢ is_couple z) -> IsFunctional (fun y => ∃ x, z = ❨x, y❩).
  Proof.
    Intros z H₁ [| y₁ y₂ [x₁ H₂] [x₂ H₃]].
    { Apply Existence.switch;
        Change (⊢ ∃ x y, _).
      Assumption. }
    { Apply Conjunction.elimination_right.
      Apply Couple.equalityₑ.
      Rewrite <- H₂.
      Rewrite <- H₃. }
  Qed.

  Theorem of_couple₁ :
    ⊢ ∀ x y, pr₁ ❨x, y❩ = x.
  Proof.
    Intros x y.
    Symmetry.
    Rewrite <- FunctionalEssence.common_term.
    { Apply Equality.reflexivity. }
    { Apply CoupleCoordinates.functional_essence₁.
      Apply Couple.couple_essence. }
  Qed.

  Theorem of_couple₂ :
    ⊢ ∀ x y, pr₂ ❨x, y❩ = y.
  Proof.
    Intros x y.
    Symmetry.
    Rewrite <- FunctionalEssence.common_term.
    { Apply Equality.reflexivity. }
    { Apply CoupleCoordinates.functional_essence₂.
      Apply Couple.couple_essence. }
  Qed.
End CoupleCoordinates.