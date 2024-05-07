Require Export
  Bourbaki.Logic.Results.All
  Bourbaki.Quantification.Results.Existence
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

Module TypicalExistence.
  Section TypicalExistence.
    Context `(QuantifiedTheory).

    (* C41_b *)
    Theorem conjunct_extraction_left 𝐑 𝐀 𝐒 :
      𝒯 ⊢ (∃ x ⟨ 𝐑 ⟩, 𝐀 ∧ 𝐒 x) ⇔ 𝐀 ∧ ∃ x ⟨ 𝐑 ⟩, 𝐒 x.
    Proof.
      unfold TypicalExistence.typical_existence at 1.
      Rewrite <- Conjunction.associativity.
      Rewrite <- (Conjunction.commutativity _ 𝐀).
      Rewrite Conjunction.associativity.
      Apply Existence.conjunct_extraction_left.
    Defined.

    (* C38_b *)
    Theorem negationₑ 𝐑 𝐒 :
      𝒯 ⊢ ¬(∃ x ⟨ 𝐒 ⟩, 𝐑 x) ⇔ ∀ x ⟨ 𝐒 ⟩, ¬𝐑 x.
    Proof.
      Rewrite Existence.negationₑ at 1.
      Rewrite Conjunction.negationₑ.
    Defined.

    (* C40_b *)
    Theorem split 𝐑 𝐒 𝐓 :
      𝒯 ⊢ (∃ x ⟨ 𝐑 ⟩, 𝐒 x ∨ 𝐓 x) ⇔ (∃ x ⟨ 𝐑 ⟩, 𝐒 x) ∨ ∃ x ⟨ 𝐑 ⟩, 𝐓 x.
    Proof.
      unfold TypicalExistence.typical_existence at 1.
      Rewrite (
        fun _ => Conjunction.distributivity_with_disjunction_left _ (𝐑 _)
      ).
      Apply Existence.split.
    Defined.

    (* C42_b *)
    Theorem switch 𝐑 𝐒 𝐓 :
      𝒯 ⊢ (∃ x ⟨ 𝐑 ⟩, ∃ y ⟨ 𝐒 ⟩, 𝐓 x y) ⇔ ∃ y ⟨ 𝐒 ⟩, ∃ x ⟨ 𝐑 ⟩, 𝐓 x y.
    Proof.
      unfold TypicalExistence.typical_existence at 1.
      Rewrite <- TypicalExistence.conjunct_extraction_left;
        Change (_ ⊢ (∃ x, ∃ y ⟨ _ ⟩, _) ⇔ _).
      Rewrite Existence.switch.
      Rewrite Existence.conjunct_extraction_left.
    Defined.
  End TypicalExistence.
End TypicalExistence.

Module TypicalQuantifier.
  Section TypicalQuantifier.
    Context `(QuantifiedTheory).

    (* C42_c *)
    Theorem interchange 𝐑 𝐒 𝐓 :
      𝒯 ⊢ (∃ x ⟨ 𝐑 ⟩, ∀ y ⟨ 𝐒 ⟩, 𝐓 x y) ⇒ ∀ y ⟨ 𝐒 ⟩, ∃ x ⟨ 𝐑 ⟩, 𝐓 x y.
    Proof.
      Intros [x H₁] y H₂ [[|]];
        plus [() | Apply H₁];
        Assumption.
    Defined.
  End TypicalQuantifier.
End TypicalQuantifier.

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

Module TypicalUniversality.
  Section TypicalUniversality.
    Context `(QuantifiedTheory).

    (* C41_a *)
    Theorem disjunct_extraction_left 𝐑 𝐀 𝐒 :
      𝒯 ⊢ (∀ x ⟨ 𝐑 ⟩, 𝐀 ∨ 𝐒 x) ⇔ 𝐀 ∨ ∀ x ⟨ 𝐑 ⟩, 𝐒 x.
    Proof.
      unfold TypicalUniversality.typical_universality at 1.
      Rewrite <- Disjunction.associativity.
      Rewrite <- (Disjunction.commutativity _ 𝐀).
      Rewrite Disjunction.associativity.
      Apply Universality.disjunct_extraction_left.
    Defined.

    (* C38_a *)
    Theorem negationₑ 𝐑 𝐒 :
      𝒯 ⊢ ¬(∀ x ⟨ 𝐒 ⟩, 𝐑 x) ⇔ ∃ x ⟨ 𝐒 ⟩, ¬𝐑 x.
    Proof.
      Rewrite Universality.negationₑ.
      Rewrite (fun _ => Implication.negationₑ _ (𝐒 _)).
    Defined.

    (* C40_a *)
    Theorem split 𝐑 𝐒 𝐓 :
      𝒯 ⊢ (∀ x ⟨ 𝐑 ⟩, 𝐒 x ∧ 𝐓 x) ⇔ (∀ x ⟨ 𝐑 ⟩, 𝐒 x) ∧ ∀ x ⟨ 𝐑 ⟩, 𝐓 x.
    Proof.
      unfold TypicalUniversality.typical_universality at 1.
      Rewrite Conjunction.as_consequenceₑ.
      Apply Universality.split.
    Defined.

    (* C42_a *)
    Theorem switch 𝐑 𝐒 𝐓 :
      𝒯 ⊢ (∀ x ⟨ 𝐑 ⟩, ∀ y ⟨ 𝐒 ⟩, 𝐓 x y) ⇔ ∀ y ⟨ 𝐒 ⟩, ∀ x ⟨ 𝐑 ⟩, 𝐓 x y.
    Proof.
      unfold TypicalUniversality.typical_universality at 1.
      Rewrite <- TypicalUniversality.disjunct_extraction_left;
        Change (_ ⊢ (∀ x, ∀ y ⟨ _ ⟩, _) ⇔ _).
      Rewrite Universality.switch.
      Rewrite Universality.disjunct_extraction_left.
    Defined.
  End TypicalUniversality.
End TypicalUniversality.