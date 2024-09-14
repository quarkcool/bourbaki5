Require Export
  Bourbaki.Set.Relation.CoupleEssence
  Bourbaki.Set.Results.Singleton.

Section Couple.
  Context `{Set_.Theory}.

  Theorem couple_essence :
    ⊢ ∀ x y, is_couple ❨x, y❩.
  Proof.
    Intros x y [[]].
    Reflexivity.
  Qed.

  (* Pr_E_II_2__1 *)
  Theorem equalityₑ :
    ⊢ ∀ x₁ x₂ y₁ y₂, ❨x₁, x₂❩ = ❨y₁, y₂❩ ⇔ x₁ = y₁ ∧ x₂ = y₂.
  Proof.
    Intros x₁ x₂ y₁ y₂.
    Rewrite Pair.equalityₑ.
    Rewrite Singleton.equalityₑ.
    Rewrite Singleton.equality_to_pair_rightₑ.
    Rewrite Singleton.equality_to_pair_leftₑ.
    Rewrite Pair.equalityₑ.
    Rewrite <- Conjunction.distributivity_over_conjunction_left.
    Rewrite <- Conjunction.distributivity_over_disjunction_left.
    Rewrite <- Disjunction.associativity.
    Rewrite Disjunction.idempotenceₑ.
    Rewrite (Conjunction.distributivity_over_disjunction_left (_ = _)).
    Rewrite (Conjunction.operand_removal_left _ (x₁ = y₁)).
    { Apply Disjunction.operand_removal_right.
      Intros [H₁ [H₂ H₃]] [|].
      { Assumption. }
      { Rewrite H₃.
        Rewrite <- H₁.
        Rewrite H₂. } }
    { Apply Conjunction.elimination_left. }
  Qed.
End Couple.