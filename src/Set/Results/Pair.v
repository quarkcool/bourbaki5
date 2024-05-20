Require Export
  Bourbaki.Equality.Results.All
  Bourbaki.Set.Results.CollectivizingSet
  Bourbaki.Set.Results.Theory
  Bourbaki.Set.Term.Pair.

Section Pair.
  Context `{SetTheory}.

  Theorem typical_existenceₑ x y 𝐑 :
    𝒯 ⊢ (∃ z ⟨ ∈ {x, y} ⟩, 𝐑 z) ⇔ 𝐑 x ∨ 𝐑 y.
  Proof.
    unfold TypicalExistence.typical_existence;
      Change (_ ⊢ (∃ z, _) ⇔ _).
    Rewrite CollectivizingSet.membershipₑ;
      Change (_ ⊢ (∃ z, _) ⇔ _).
    Rewrite (
      fun _ => Conjunction.distributivity_with_disjunction_right _ (_ = _)
    ).
    Rewrite Existence.split;
      Change (_ ⊢ (∃ z, _) ∨ (∃ z, _) ⇔ _).
    Rewrite Existence.of_equal.
  Defined.

  Theorem typical_universalityₑ x y 𝐑 :
    𝒯 ⊢ (∀ z ⟨ ∈ {x, y} ⟩, 𝐑 z) ⇔ 𝐑 x ∧ 𝐑 y.
  Proof.
    unfold TypicalUniversality.typical_universality;
      Change (_ ⊢ (∀ z, _) ⇔ _).
    Rewrite CollectivizingSet.membershipₑ;
      Change (_ ⊢ (∀ z, _) ⇔ _).
    Rewrite Disjunction.as_conditionₑ.
    Rewrite Universality.split;
      Change (_ ⊢ (∀ z, _) ∧ (∀ z, _) ⇔ _).
    Rewrite Universality.over_equals.
  Defined.

  Theorem unordered_essence x y :
    𝒯 ⊢ {x, y} = {y, x}.
  Proof.
    Apply CollectivizingSet.equalityₑ.
    Intros z.
    Apply Disjunction.commutativity.
  Defined.
End Pair.