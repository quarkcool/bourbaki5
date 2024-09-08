Require Export
  Bourbaki.Set.Relation.Emptiness
  Bourbaki.Set.Results.CollectivizingSubset
  Bourbaki.Set.Results.Meta.Complement.

Section Complement.
  Context `{Set_.Theory}.

  Theorem double_removalₑ {X} A :
    ⊢ ∁ X (∁ X A) = A.
  Proof.
    Apply Set_.equalityₑ.
    Intros x.
    do 2 (unfold non_membership; Rewrite MembershipEquivalenceProof.proof).
    Rewrite Conjunction.negationₑ.
    Rewrite Negation.double_removalₑ.
    Rewrite (Conjunction.distributivity_over_disjunction_right (_ ∈ _)).
    Rewrite Disjunction.operand_removal_right.
    { Apply Conjunction.operand_removal_right.
      Apply Subset.subset_essence. }
    { Intros H₁.
      Exfalso.
      Apply Conjunction.impossibility.
      Apply Conjunction.symmetry.
      Assumption. }
  Qed.

  Theorem inclusionₑ {x} (a b : Subset x) :
    ⊢ a ⊂ b ⇔ ∁ x b ⊂ ∁ x a.
  Proof.
    Intros [H₁ | H₁].
    { Rewrite H₁. }
    { Rewrite <- Complement.double_removalₑ.
      Rewrite H₁. }
  Qed.

  Theorem of_set_relative_to_itself_emptiness :
    ⊢ ∀ x, is_empty (∁ x x).
  Proof.
    Intros X x.
    unfold non_membership; Rewrite MembershipEquivalenceProof.proof.
    Rewrite Conjunction.commutativity.
    Apply Conjunction.impossibility.
  Qed.
End Complement.