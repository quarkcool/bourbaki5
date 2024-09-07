Require Export
  Bourbaki.Equality.Results.Equality
  Bourbaki.Equality.Results.FunctionalEssence
  Bourbaki.Quantification.Results.All.

Module Existence.
  Section Existence.
    Context `{Equality.Theory}.

    (* Ex_E_I_5__2 *)
    Theorem of_equalₑ 𝐑 :
      ⊢ ∀ y, (∃ x ⟨= y⟩, 𝐑 x) ⇔ 𝐑 y.
    Proof.
      unfold typical_existence.
      Intros y.
      Rewrite Equality.as_conjunct_leftₑ.
      Rewrite Existence.conjunct_extraction_right.
      Apply Conjunction.operand_removal_left.
      Apply Equality.reflexivity.
    Qed.
  End Existence.
End Existence.

Module TypicalExistence.
  Section TypicalExistence.
    Context `{Equality.Theory}.

    Theorem of_equalₑ 𝐑 𝐒 :
      ⊢ ∀ y, (∃ x ⟨𝐑⟩, x = y ∧ 𝐒 x) ⇔ 𝐑 y ∧ 𝐒 y.
    Proof.
      unfold typical_existence.
      Intros y.
      Rewrite Conjunction.associativity.
      Rewrite <- (fun _ => Conjunction.commutativity (_ = _)).
      Rewrite <- Conjunction.associativity.
      Apply Existence.of_equalₑ.
    Qed.
  End TypicalExistence.
End TypicalExistence.

Module Universality.
  Section Universality.
    Context `{Equality.Theory}.

    Theorem over_equalsₑ 𝐑 :
      ⊢ ∀ y, (∀ x ⟨= y⟩, 𝐑 x) ⇔ 𝐑 y.
    Proof.
      unfold typical_universality.
      Intros y.
      Rewrite Equality.as_conditionₑ.
      Rewrite Universality.consequence_extraction.
      Apply Implication.with_true_condition.
      Apply Equality.reflexivity.
    Qed.
  End Universality.
End Universality.

Module TypicalUniversality.
  Section TypicalUniversality.
    Context `{Equality.Theory}.

    Theorem over_equalsₑ 𝐑 𝐒 :
      ⊢ ∀ y, (∀ x ⟨𝐑⟩, x = y ⇒ 𝐒 x) ⇔ 𝐑 y ⇒ 𝐒 y.
    Proof.
      unfold typical_universality.
      Intros y.
      Rewrite Implication.condition_commutativity.
      Apply Universality.over_equalsₑ.
    Qed.
  End TypicalUniversality.
End TypicalUniversality.

Module Other.
  Section Other.
    Context `{Equality.Theory}.

    Lemma Th_E_I_5__3 :
      ⊢ ∀ x y z, x = y ∧ y = z ⇒ x = z.
    Proof.
      Rewrite Conjunction.as_conditionₑ.
      Apply Equality.transitivity.
    Qed.

    Lemma C47 {𝐑} 𝐒 `(!IsFunctional 𝐑) :
      ⊢ 𝐒 (τ x, 𝐑 x) ⇔ ∃ x, 𝐑 x ∧ 𝐒 x.
    Proof.
      Rewrite (FunctionalEssence.common_term (𝐑 := 𝐑)) at 2.
      Rewrite Existence.of_equalₑ.
    Qed.

    Lemma Ex_E_I_5__3 {𝐒 : Term -> _} {𝐑 T} :
      (forall y, (⊢ 𝐒 y) -> IsFunctional (fun x => 𝐑 x y)) -> (⊢ 𝐒 T) ->
        IsFunctional (fun x => 𝐑 x T).
    Proof.
      Intros H₁.
      Assumption.
    Qed.

    Lemma Ex_E_I_5__5_i {𝐑} 𝐒 `(!IsFunctional 𝐑) :
      ⊢ ¬(∃ x, 𝐑 x ∧ 𝐒 x) ⇔ ∃ x, 𝐑 x ∧ ¬𝐒 x.
    Proof.
      Rewrite (FunctionalEssence.common_term (𝐑 := 𝐑)).
      Rewrite Existence.of_equalₑ.
    Qed.

    Lemma Ex_E_I_5__5_ii {𝐑} 𝐒 𝐓 `(!IsFunctional 𝐑) :
      ⊢ (∃ x, 𝐑 x ∧ 𝐒 x ∧ 𝐓 x) ⇔ (∃ x, 𝐑 x ∧ 𝐒 x) ∧ ∃ x, 𝐑 x ∧ 𝐓 x.
    Proof.
      Rewrite (FunctionalEssence.common_term (𝐑 := 𝐑)).
      Rewrite Existence.of_equalₑ.
    Qed.

    Lemma Ex_E_I_5__5_iii 𝐑 𝐒 𝐓 :
      ⊢ (∃ x, 𝐑 x ∧ 𝐒 x ∨ 𝐓 x) ⇔ (∃ x, 𝐑 x ∧ 𝐒 x) ∨ ∃ x, 𝐑 x ∧ 𝐓 x.
    Proof.
      Apply TypicalExistence.split.
    Qed.
  End Other.
End Other.