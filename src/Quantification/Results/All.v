Require Export
  Bourbaki.Logic.Results.All
  Bourbaki.Quantification.Results.Meta.Rewriting
  Bourbaki.Quantification.Results.Universality.

Import Proof.TheoryHidingNotation.

Module Existence.
  Section Existence.
    Context `(QuantifiedTheory).

    (* C33_b *)
    Theorem conjunct_extraction_left 𝐀 𝐑 :
      𝒯 ⊢ (∃ x, 𝐀 ∧ 𝐑 x) ⇔ 𝐀 ∧ ∃ x, 𝐑 x.
    Proof.
      Intros [[x H₁] [|] | H₁ [[|]]];
        Assumption.
    Defined.

    Theorem conjunct_extraction_right 𝐑 𝐀 :
      𝒯 ⊢ (∃ x, 𝐑 x ∧ 𝐀) ⇔ (∃ x, 𝐑 x) ∧ 𝐀.
    Proof.
      Rewrite <- (Conjunction.commutativity _ 𝐀).
      Apply Existence.conjunct_extraction_left.
    Defined.

    (* C29 *)
    Theorem negationₑ 𝐑 :
      𝒯 ⊢ ¬(∃ x, 𝐑 x) ⇔ ∀ x, ¬𝐑 x.
    Proof.
      unfold Universality.universality.
      Rewrite Negation.double_removal.
    Defined.

    (* C32_b *)
    Theorem split 𝐑 𝐒 :
      𝒯 ⊢ (∃ x, 𝐑 x ∨ 𝐒 x) ⇔ (∃ x, 𝐑 x) ∨ ∃ x, 𝐒 x.
    Proof.
      Intros [[x [H₁ | H₁]] | [H₁ | H₁]];
        Assumption.
    Defined.
  End Existence.
End Existence.

Module Quantifier.
  Section Quantifier.
    Context `(QuantifiedTheory).

    (* C34_c *)
    Theorem interchange 𝐑 :
      𝒯 ⊢ (∃ x, ∀ y, 𝐑 x y) ⇒ ∀ y, ∃ x, 𝐑 x y.
    Proof.
      Intros [x H₁] y.
      Assumption.
    Defined.
  End Quantifier.
End Quantifier.

Module Universality.
  Section Universality.
    Context `(QuantifiedTheory).

    (* C33_a *)
    Theorem disjunct_extraction_left 𝐀 𝐑 :
      𝒯 ⊢ (∀ x, 𝐀 ∨ 𝐑 x) ⇔ 𝐀 ∨ ∀ x, 𝐑 x.
    Proof.
      Rewrite <- (Negation.double_removal _ (∀ x, _)).
      Rewrite Universality.negationₑ.
      Rewrite (Disjunction.negationₑ _ 𝐀).
      Rewrite Existence.conjunct_extraction_left.
      Rewrite Conjunction.negationₑ.
      Rewrite Negation.double_removal.
    Defined.

    Theorem disjunct_extraction_right 𝐀 𝐑 :
      𝒯 ⊢ (∀ x, 𝐑 x ∨ 𝐀) ⇔ (∀ x, 𝐑 x) ∨ 𝐀.
    Proof.
      Rewrite Disjunction.commutativity.
      Apply Universality.disjunct_extraction_left.
    Defined.

    Theorem consequence_extraction 𝐑 𝐀 :
      𝒯 ⊢ (∀ x, 𝐑 x ⇒ 𝐀) ⇔ (∃ x, 𝐑 x) ⇒ 𝐀.
    Proof.
      unfold Implication.implication at 2.
      Rewrite Universality.disjunct_extraction_right.
      Rewrite (Existence.negationₑ _ 𝐑).
    Defined.

    (* C32_a *)
    Theorem split 𝐑 𝐒 :
      𝒯 ⊢ (∀ x, 𝐑 x ∧ 𝐒 x) ⇔ (∀ x, 𝐑 x) ∧ ∀ x, 𝐒 x.
    Proof.
      Intros [H₁ [x | x] | H₁ x [|]];
        Assumption.
    Defined.
  End Universality.
End Universality.