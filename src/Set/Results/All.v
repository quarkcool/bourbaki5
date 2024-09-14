Require Export
  Bourbaki.Equality.Relation.Inequality
  Bourbaki.Set.Relation.NonEmptiness
  Bourbaki.Set.Results.CollectivizingEssence
  Bourbaki.Set.Results.EmptySet.

Module Complement.
  Section Complement.
    Context `{Set_.Theory}.

    Theorem of_empty_set :
      ⊢ ∀ x, ∁ x ∅ = x.
    Proof.
      Rewrite Set_.equalityₑ.
      Intros X x.
      Rewrite MembershipEquivalenceProof.proof.
      Apply Conjunction.operand_removal_left.
      Apply EmptySet.emptiness.
    Qed.

    Theorem of_set_relative_to_itself :
      ⊢ ∀ x, ∁ x x = ∅.
    Proof.
      Rewrite EmptySet.as_equalₑ.
      Apply Complement.of_set_relative_to_itself_emptiness.
    Qed.
  End Complement.
End Complement.

Module NonEmptiness.
  Section NonEmptiness.
    Context `{Set_.Theory}.

    Theorem alternative_definition :
      ⊢ ∀ x, is_non_empty x ⇔ ¬is_empty x.
    Proof.
      Intros X.
      Rewrite Universality.negationₑ.
      Rewrite Negation.double_removalₑ.
    Qed.

    Theorem alternative_definition₂ :
      ⊢ ∀ x, is_non_empty x ⇔ x ≠ ∅.
    Proof.
      Intros x.
      unfold inequality.
      Rewrite EmptySet.as_equalₑ.
      Apply NonEmptiness.alternative_definition.
    Qed.
  End NonEmptiness.
End NonEmptiness.

Module Singleton.
  Section Singleton.
    Context `{Set_.Theory}.

    (* Ex_E_II_1__4 *)
    Theorem as_supersetₑ {X x} :
      ⊢ X ⊂ {x,} ⇔ X = {x,} ∨ X = ∅.
    Proof.
      Rewrite Set_.equalityₑ₂ at 1.
      Rewrite Singleton.as_subsetₑ.
      Rewrite Disjunction.distributivity_over_conjunction_right.
      Rewrite (Disjunction.operand_removal_right _ (_ ⊂ _)).
      { Rewrite (Conjunction.operand_removal_right (_ ⊂ _)).
        Rewrite (Disjunction.commutativity (_ ∈ _)).
        Rewrite <- (Negation.as_conditionₑ (_ = _)).
        Rewrite <- NonEmptiness.alternative_definition₂.
        Intros H₁ [y H₂].
        Rewrite <- (_ : y ⊢= x).
        { Apply (MembershipEquivalenceProof.proof _ (fun y => y = x)).
          Apply H₁.
          Assumption. }
        { Assumption. } }
      { Intros H₁.
        Rewrite H₁.
        Apply EmptySet.subset_essence. }
    Qed.
  End Singleton.
End Singleton.

Module Other.
  Section Other.
    Context `{Set_.Theory}.

    Lemma Pr_E_II_1__2 :
      ⊢ ∀ x y z, x ⊂ y ∧ y ⊂ z ⇒ x ⊂ z.
    Proof.
      Rewrite Conjunction.as_conditionₑ.
      Apply Inclusion.transitivity.
    Qed.

    Lemma Exa_E_II_1_4__2 :
      ⊢ ¬Coll (fun x => x ∉ x).
    Proof.
      Intros [X contra₁].
      Apply Equivalence.impossibility.
      Assumption.
    Qed.

    Lemma C50_i {𝐑 𝐒} `(!IsCollectivizing 𝐑) `(!IsCollectivizing 𝐒) :
      ⊢ (∀ x, 𝐑 x ⇒ 𝐒 x) ⇔ {x | 𝐑 x} ⊂ {x | 𝐒 x}.
    Proof.
      Rewrite CollectivizingSet.inclusionₑ.
    Qed.

    Lemma C50_ii {𝐑 𝐒} `(!IsCollectivizing 𝐑) `(!IsCollectivizing 𝐒) :
      ⊢ (∀ x, 𝐑 x ⇔ 𝐒 x) ⇔ {x | 𝐑 x} = {x | 𝐒 x}.
    Proof.
      Rewrite CollectivizingSet.equalityₑ.
    Qed.

    Lemma Rem_E_II_1__1 𝐒 {𝐑} `(!IsCollectivizing 𝐑) :
      (⊢ ∀ x, 𝐒 x ⇒ 𝐑 x) -> IsCollectivizing 𝐒.
    Proof.
      Intros H₁.
      Apply CollectivizingEssence.from_container_set.
      Intros x.
      Rewrite (MembershipEquivalenceProof.proof {x | 𝐑 x}).
      Assumption.
    Qed.

    Lemma Rem_E_II_1__2 :
      ⊢ ¬∃ X, ∀ x, x ∈ X.
    Proof.
      Intros [X contra₁].
      Apply Other.Exa_E_II_1_4__2.
      Apply CollectivizingEssence.from_container_set.
      Intros x _.
      Assumption.
    Qed.

    Lemma Ex_E_II_1__1 x y :
      ⊢ x = y ⇔ ∀ X, x ∈ X ⇒ y ∈ X.
    Proof.
      Intros [H₁ X | H₁].
      { Rewrite H₁. }
      { Symmetry.
        Apply (MembershipEquivalenceProof.proof _ (fun y => y = x)).
        Apply H₁.
        Apply MembershipEquivalenceProof.proof.
        Reflexivity. }
    Qed.

    Lemma Ex_E_II_1__2_i x :
      ⊢ ∅ ≠ {x,}.
    Proof.
      Intros contra₁.
      Apply EmptySet.emptiness; Change (⊢ _ ∈ _).
      Rewrite contra₁.
      Apply MembershipEquivalenceProof.proof.
      Reflexivity.
    Qed.

    Lemma Ex_E_II_1__2_ii :
      ⊢ ∃ x y, x ≠ y.
    Proof.
      Apply Other.Ex_E_II_1__2_i.
      Apply Util.default.
    Qed.

    Lemma Ex_E_II_1__5 :
      ⊢ ∅ = τ X, (τ x, x ∈ X) ∉ X.
    Proof.
      unfold empty_set;
        Change (⊢ (τ X, _) = _).
      Rewrite Universality.alternative_definition.
      Rewrite Negation.double_removalₑ.
    Qed.
  End Other.

  Section Ex_E_II_1__6.
    Context `{Equality.Theory, !Set_.Syntax}.
    Context (A1' : ⊢ ∀ y, y = τ x, ∀ z, z ∈ x ⇔ z ∈ y).

    Lemma Ex_E_II_1__6 :
      ⊢ ∀ x y, x ⊂ y ⇒ y ⊂ x ⇒ x = y.
    Proof.
      Intros X Y H₁ H₂.
      Rewrite A1'.
      Rewrite (_ : ⊢ ∀ z, z ∈ X ⇔ z ∈ Y).
      Apply Universality.split.
      Intros [|];
        Assumption.
    Qed.
  End Ex_E_II_1__6.
End Other.