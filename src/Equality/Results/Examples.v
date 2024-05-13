Require Export
  Bourbaki.Equality.Relation.Inequality
  Bourbaki.Equality.Results.All
  Bourbaki.Equality.Results.FunctionalRelation.

Import Proof.TheoryHidingNotation.

Section Examples.
  Context `(EqualitarianTheory).

  Example TH3 x y z :
    𝒯 ⊢ x = y ∧ y = z ⇒ x = z.
  Proof.
    Rewrite Conjunction.as_conditionₑ.
    Apply Equality.transitivity.
  Defined.

  Example C44 T U V :
    𝒯 ⊢ T = U ⇒ V T = V U.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C47 {𝐑} `(!FunctionalRelation 𝒯 𝐑) 𝐒 :
    𝒯 ⊢ 𝐒 (τ x, 𝐑 x) ⇔ ∃ x ⟨ 𝐑 ⟩, 𝐒 x.
  Proof.
    unfold TypicalExistence.typical_existence.
    Rewrite (FunctionalRelation.unique_value (𝐑 := 𝐑)) at 2.
    Rewrite Existence.of_equal.
  Defined.

  Example EX_I_5_2 y 𝐑 :
    𝒯 ⊢ (∃ x, x = y ∧ 𝐑 x) ⇔ 𝐑 y.
  Proof.
    Apply Existence.of_equal.
  Defined.

  Example EX_I_5_3 {𝐒 : Term -> Term -> _} {𝐑 T} :
    (forall x y, FunctionalRelation (𝐒 x y ∷ 𝒯) (fun x => 𝐑 x y)) ->
    (forall x, 𝒯 ⊢ 𝐒 x T) ->
      FunctionalRelation 𝒯 (fun x => 𝐑 x T).
  Proof.
    Intros H₁ H₂ 𝒯' H₃.
    Apply FunctionalRelation.functional_essence;
      Change (_ ⟫ 𝐒 T T ∷ _).
    split.
    { Intros 𝐀 [H₄ | H₄].
      { rewrite H₄.
        Assumption. }
      { Assumption. } }
    { simpl.
      Apply StrongerTheoryEssence.weaker_schema. }
  Defined.

  Example EX_I_5_4 {𝐑 𝐒} :
    FunctionalRelation 𝒯 𝐑 -> (forall x, 𝒯 ⊢ 𝐑 x ⇔ 𝐒 x) ->
      FunctionalRelation 𝒯 𝐒.
  Proof.
    Intros H₁ H₂.
    Change (FunctionalRelation 𝒯 (fun x => _)).
    Rewrite <- H₂.
  Defined.

  Example EX_I_5_5_a {𝐑} 𝐒 `(!FunctionalRelation 𝒯 𝐑) :
    𝒯 ⊢ ¬(∃ x ⟨ 𝐑 ⟩, 𝐒 x) ⇔ ∃ x ⟨ 𝐑 ⟩, ¬𝐒 x.
  Proof.
    unfold TypicalExistence.typical_existence.
    Rewrite (FunctionalRelation.unique_value (𝐑 := 𝐑)).
    Rewrite Existence.of_equal.
  Defined.

  Example EX_I_5_5_b {𝐑} 𝐒 𝐓 `(!FunctionalRelation 𝒯 𝐑) :
    𝒯 ⊢ (∃ x ⟨ 𝐑 ⟩, 𝐒 x ∧ 𝐓 x) ⇔ (∃ x ⟨ 𝐑 ⟩, 𝐒 x) ∧ ∃ x ⟨ 𝐑 ⟩, 𝐓 x.
  Proof.
    unfold TypicalExistence.typical_existence.
    Rewrite (FunctionalRelation.unique_value (𝐑 := 𝐑)).
    Rewrite Existence.of_equal.
  Defined.

  Example EX_I_5_5_c {𝐑} 𝐒 𝐓 `(!FunctionalRelation 𝒯 𝐑) :
    𝒯 ⊢ (∃ x ⟨ 𝐑 ⟩, 𝐒 x ∨ 𝐓 x) ⇔ (∃ x ⟨ 𝐑 ⟩, 𝐒 x) ∨ ∃ x ⟨ 𝐑 ⟩, 𝐓 x.
  Proof.
    Apply TypicalExistence.split.
  Defined.

  Example EX_I_5_6 {x y} (H₁ : 𝒯 ⊢ x ≠ y) :
    (forall 𝐑 x, 𝒯 ⊢ (∃ x, 𝐑 x) ⇒ 𝐑 x) -> Contradictory 𝒯.
  Proof.
    Intros H₂.
    do 2 esplit.
    2: Assumption.
    { Apply (H₂ (fun y => x = y));
        Change (_ ⊢ ∃ z, _ = z).
      Apply Equality.reflexivity. }
  Defined.

  Example EX_I_5_7 {x y} (H₁ : 𝒯 ⊢ x ≠ y) :
    (forall 𝐑 𝐒 x, 𝒯 ⊢ (𝐑 x ⇔ 𝐒 x) ⇒ (τ x, 𝐑 x) = τ x, 𝐒 x) ->
      Contradictory 𝒯.
  Proof.
    Intros H₂.
    do 2 esplit.
    { admit. }
  Admitted.
End Examples.