Require Export
  Bourbaki.Equality.Results.Equality
  Bourbaki.Logic.Results.Implication
  Bourbaki.Quantification.Results.All.

Import Proof.TheoryHidingNotation.

Module Existence.
  Section Existence.
    Context `(EqualitarianTheory).

    Theorem of_equal 𝐑 :
      𝒯 ⊢ ∀ y, (∃ x, x = y ∧ 𝐑 x) ⇔ 𝐑 y.
    Proof.
      Intros y.
      Rewrite Equality.as_conjunct_leftₑ.
      Rewrite Existence.conjunct_extraction_right.
      Apply Conjunction.operand_removal_leftₑ.
      Apply Equality.reflexivity.
    Defined.
  End Existence.
End Existence.

Module Universality.
  Section Universality.
    Context `(EqualitarianTheory).

    Theorem over_equals 𝐑 :
      𝒯 ⊢ ∀ y, (∀ x, x = y ⇒ 𝐑 x) ⇔ 𝐑 y.
    Proof.
      Intros y.
      Rewrite Equality.as_conditionₑ.
      Rewrite Universality.consequence_extraction.
      Apply Implication.with_true_condition.
      Apply Equality.reflexivity.
    Defined.
  End Universality.
End Universality.