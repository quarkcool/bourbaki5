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
  End Other.
End Other.