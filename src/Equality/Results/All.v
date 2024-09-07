Require Export
  Bourbaki.Equality.Results.Equality
  Bourbaki.Quantification.Results.All.

Module Existence.
  Section Existence.
    Context `{Equality.Theory}.

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
  End Other.
End Other.