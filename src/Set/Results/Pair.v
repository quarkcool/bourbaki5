Require Export
  Bourbaki.Equality.Results.All
  Bourbaki.Set.Results.CollectivizingSet
  Bourbaki.Set.Results.Set
  Bourbaki.Set.Term.Pair.

Section Pair.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall x y, IsCollectivizing (fun z => z = x ∨ z = y).
  Proof.
    Intros x y.
    Apply Set_.two_element_set.
  Qed.

  Theorem typical_universalityₑ 𝐑 :
    ⊢ ∀ x y, (∀ z ⟨∈ {x, y}⟩, 𝐑 z) ⇔ 𝐑 x ∧ 𝐑 y.
  Proof.
    unfold typical_universality;
      Change (⊢ ∀ x y, (∀ z, _) ⇔ _).
    Intros x y.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite Disjunction.as_conditionₑ.
    Rewrite Universality.split;
      Change (⊢ (∀ z, _) ∧ (∀ z, _) ⇔ _).
    Rewrite Universality.over_equalsₑ.
  Qed.

  Theorem as_subsetₑ :
    ⊢ ∀ x y X, {x, y} ⊂ X ⇔ x ∈ X ∧ y ∈ X.
  Proof.
    Intros x y X.
    Apply Pair.typical_universalityₑ.
  Qed.

  Theorem equalityₑ :
    ⊢ ∀ x₁ x₂ y₁ y₂,
      {x₁, x₂} = {y₁, y₂} ⇔ (x₁ = y₁ ∧ x₂ = y₂) ∨ x₁ = y₂ ∧ x₂ = y₁.
  Proof.
    Intros x₁ x₂ y₁ y₂.
    Rewrite Set_.equalityₑ₂ at 1.
    Rewrite Pair.as_subsetₑ.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite <- (⇑Equality.commutativity x₁).
    Rewrite <- (⇑Equality.commutativity x₂).
    Rewrite <- (Disjunction.commutativity (x₂ = y₂)).
    Rewrite <- Conjunction.associativity.
    Rewrite (Conjunction.commutativity ((x₂ = y₂) ∨ _)).
    Rewrite <- Conjunction.associativity.
    Rewrite Conjunction.associativity.
    Rewrite <- Disjunction.distributivity_over_conjunction_left.
    Rewrite <- Disjunction.distributivity_over_conjunction_right.
  Qed.

  Theorem typical_existenceₑ 𝐑 :
    ⊢ ∀ x y, (∃ z ⟨∈ {x, y}⟩, 𝐑 z) ⇔ 𝐑 x ∨ 𝐑 y.
  Proof.
    unfold typical_existence;
      Change (⊢ ∀ x y, (∃ z, _) ⇔ _).
    Intros x y.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite (
      fun _ => Conjunction.distributivity_over_disjunction_right _ _ (𝐑 _)
    ).
    Rewrite Existence.split;
      Change (⊢ (∃ z, _) ∨ (∃ z, _) ⇔ _).
    Rewrite Existence.of_equalₑ.
  Qed.

  Theorem unordered_essence :
    ⊢ ∀ x y, {x, y} = {y, x}.
  Proof.
    Rewrite Set_.equalityₑ.
    Intros x y z.
    Rewrite MembershipEquivalenceProof.proof.
    Apply Disjunction.commutativity.
  Qed.
End Pair.