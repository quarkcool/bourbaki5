Require Export
  Bourbaki.Logic.Results.All
  Bourbaki.Meta.Tactic.Change
  Bourbaki.Quantification.Relation.TypicalUniversality
  Bourbaki.Quantification.Results.Meta.TypicalExistence
  Bourbaki.Quantification.Results.Universality.

Module Existence.
  Section Existence.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    (* C33_ii *)
    Theorem conjunct_extraction_left 𝐀 𝐑 :
      ⊢ (∃ x, 𝐀 ∧ 𝐑 x) ⇔ 𝐀 ∧ ∃ x, 𝐑 x.
    Proof.
      Intros [[x H₁] [|] | [H₁ [x H₂]] [[|]]];
        Assumption.
    Qed.

    Theorem conjunct_extraction_right 𝐑 𝐀 :
      ⊢ (∃ x, 𝐑 x ∧ 𝐀) ⇔ (∃ x, 𝐑 x) ∧ 𝐀.
    Proof.
      Rewrite <- (Conjunction.commutativity 𝐀).
      Apply Existence.conjunct_extraction_left.
    Qed.

    (* C29 *)
    Theorem negationₑ 𝐑 :
      ⊢ ¬(∃ x, 𝐑 x) ⇔ ∀ x, ¬𝐑 x.
    Proof.
      unfold universality.
      Rewrite Negation.double_removalₑ.
    Qed.

    (* C32_ii *)
    Theorem split 𝐑 𝐒 :
      ⊢ (∃ x, 𝐑 x ∨ 𝐒 x) ⇔ (∃ x, 𝐑 x) ∨ ∃ x, 𝐒 x.
    Proof.
      Intros [[x [H₁ | H₁]] | [[x H₁] | [x H₁]]];
        Assumption.
    Qed.
  End Existence.
End Existence.

Module TypicalExistence.
  Section TypicalExistence.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    (* C41_ii *)
    Theorem conjunct_extraction_left 𝐑 𝐀 𝐒 :
      ⊢ (∃ x ⟨𝐑⟩, 𝐀 ∧ 𝐒 x) ⇔ 𝐀 ∧ ∃ x ⟨𝐑⟩, 𝐒 x.
    Proof.
      unfold typical_existence at 1.
      Rewrite Conjunction.associativity.
      Rewrite <- (Conjunction.commutativity 𝐀).
      Rewrite <- Conjunction.associativity.
      Apply Existence.conjunct_extraction_left.
    Qed.

    Theorem conjunct_extraction_right 𝐑 𝐀 𝐒 :
      ⊢ (∃ x ⟨𝐑⟩, 𝐒 x ∧ 𝐀) ⇔ (∃ x ⟨𝐑⟩, 𝐒 x) ∧ 𝐀.
    Proof.
      Rewrite <- (Conjunction.commutativity 𝐀).
      Apply TypicalExistence.conjunct_extraction_left.
    Qed.

    (* C38_ii *)
    Theorem negationₑ 𝐑 𝐒 :
      ⊢ ¬(∃ x ⟨𝐑⟩, 𝐒 x) ⇔ ∀ x ⟨𝐑⟩, ¬𝐒 x.
    Proof.
      Rewrite Existence.negationₑ at 1.
      Rewrite Conjunction.negationₑ at 1.
    Qed.

    (* C40_ii *)
    Theorem split 𝐑 𝐒₁ 𝐒₂ :
      ⊢ (∃ x ⟨𝐑⟩, 𝐒₁ x ∨ 𝐒₂ x) ⇔ (∃ x ⟨𝐑⟩, 𝐒₁ x) ∨ ∃ x ⟨𝐑⟩, 𝐒₂ x.
    Proof.
      unfold typical_existence at 1.
      Rewrite (
        fun _ => Conjunction.distributivity_over_disjunction_left (𝐑 _)
      ).
      Apply Existence.split.
    Qed.

    (* C42_ii *)
    Theorem switch 𝐑₁ 𝐑₂ 𝐒 :
      ⊢ (∃ x ⟨𝐑₁⟩, ∃ y ⟨𝐑₂⟩, 𝐒 x y) ⇔ ∃ y ⟨𝐑₂⟩, ∃ x ⟨𝐑₁⟩, 𝐒 x y.
    Proof.
      unfold typical_existence at 1.
      Rewrite <- TypicalExistence.conjunct_extraction_left;
        Change (⊢ (∃ x, ∃ y ⟨_⟩, _) ⇔ _).
      Rewrite Existence.switch.
      Rewrite Existence.conjunct_extraction_left.
    Qed.

    Theorem switch_with_atypical 𝐑 𝐒 :
      ⊢ (∃ x ⟨𝐑⟩, ∃ y, 𝐒 x y) ⇔ ∃ y, ∃ x ⟨𝐑⟩, 𝐒 x y.
    Proof.
      Rewrite Existence.switch;
        Change (⊢ _ ⇔ ∃ x y, _).
      Rewrite Existence.conjunct_extraction_left.
    Qed.
  End TypicalExistence.
End TypicalExistence.

Module Universality.
  Section Universality.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    (* C33_i *)
    Theorem disjunct_extraction_left 𝐀 𝐑 :
      ⊢ (∀ x, 𝐀 ∨ 𝐑 x) ⇔ 𝐀 ∨ ∀ x, 𝐑 x.
    Proof.
      unfold universality.
      Rewrite (Disjunction.negationₑ 𝐀).
      Rewrite Existence.conjunct_extraction_left.
      Rewrite Conjunction.negationₑ.
      Rewrite Negation.double_removalₑ.
    Qed.

    Theorem condition_extraction 𝐀 𝐑 :
      ⊢ (∀ x, 𝐀 ⇒ 𝐑 x) ⇔ 𝐀 ⇒ ∀ x, 𝐑 x.
    Proof.
      Apply Universality.disjunct_extraction_left.
    Qed.

    Theorem consequence_extraction 𝐑 𝐀 :
      ⊢ (∀ x, 𝐑 x ⇒ 𝐀) ⇔ (∃ x, 𝐑 x) ⇒ 𝐀.
    Proof.
      Intros [H₁ [x H₂] | H₁ x H₂];
        Apply H₁;
        Assumption.
    Qed.

    (* C32_i *)
    Theorem split 𝐑 𝐒 :
      ⊢ (∀ x, 𝐑 x ∧ 𝐒 x) ⇔ (∀ x, 𝐑 x) ∧ ∀ x, 𝐒 x.
    Proof.
      Intros [H₁ [x | x] | H₁ x [|]];
        Assumption.
    Qed.
  End Universality.
End Universality.

Module TypicalUniversality.
  Section TypicalUniversality.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    Theorem alternative_definition 𝐑 𝐒 :
      ⊢ (∀ x ⟨𝐑⟩, 𝐒 x) ⇔ ¬∃ x ⟨𝐑⟩, ¬𝐒 x.
    Proof.
      unfold typical_universality, universality.
      Rewrite (fun _ => Implication.negationₑ (𝐑 _)).
    Qed.

    (* C41_i *)
    Theorem disjunct_extraction_left 𝐑 𝐀 𝐒 :
      ⊢ (∀ x ⟨𝐑⟩, 𝐀 ∨ 𝐒 x) ⇔ 𝐀 ∨ ∀ x ⟨𝐑⟩, 𝐒 x.
    Proof.
      Rewrite TypicalUniversality.alternative_definition.
      Rewrite (Disjunction.negationₑ 𝐀).
      Rewrite TypicalExistence.conjunct_extraction_left.
      Rewrite (Conjunction.negationₑ (¬𝐀)).
      Rewrite Negation.double_removalₑ.
    Qed.

    Theorem condition_extraction 𝐑 𝐀 𝐒 :
      ⊢ (∀ x ⟨𝐑⟩, 𝐀 ⇒ 𝐒 x) ⇔ 𝐀 ⇒ ∀ x ⟨𝐑⟩, 𝐒 x.
    Proof.
      Apply TypicalUniversality.disjunct_extraction_left.
    Qed.

    (* C38_i *)
    Theorem negationₑ 𝐑 𝐒 :
      ⊢ ¬(∀ x ⟨𝐑⟩, 𝐒 x) ⇔ ∃ x ⟨𝐑⟩, ¬𝐒 x.
    Proof.
      Rewrite TypicalUniversality.alternative_definition.
      Apply Negation.double_removalₑ.
    Qed.

    (* C40_i *)
    Theorem split 𝐑 𝐒₁ 𝐒₂ :
      ⊢ (∀ x ⟨𝐑⟩, 𝐒₁ x ∧ 𝐒₂ x) ⇔ (∀ x ⟨𝐑⟩, 𝐒₁ x) ∧ ∀ x ⟨𝐑⟩, 𝐒₂ x.
    Proof.
      unfold typical_universality at 1.
      Rewrite Conjunction.as_consequenceₑ.
      Apply Universality.split.
    Qed.

    (* C42_i *)
    Theorem switch 𝐑₁ 𝐑₂ 𝐒 :
      ⊢ (∀ x ⟨𝐑₁⟩, ∀ y ⟨𝐑₂⟩, 𝐒 x y) ⇔ ∀ y ⟨𝐑₂⟩, ∀ x ⟨𝐑₁⟩, 𝐒 x y.
    Proof.
      unfold typical_universality at 1.
      Rewrite <- TypicalUniversality.condition_extraction;
        Change (⊢ (∀ x, ∀ y ⟨_⟩, _) ⇔ _).
      Rewrite Universality.switch.
      Rewrite Universality.condition_extraction.
    Qed.
  End TypicalUniversality.
End TypicalUniversality.

Module Other.
  Section Other.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    Lemma C34_iii 𝐑 :
      ⊢ (∃ x, ∀ y, 𝐑 x y) ⇒ ∀ y, ∃ x, 𝐑 x y.
    Proof.
      Intros [x H₁] y.
      Assumption.
    Qed.

    Lemma C35 𝐑 𝐒 :
      ⊢ (∀ x ⟨𝐑⟩, 𝐒 x) ⇔ ∀ x, 𝐑 x ⇒ 𝐒 x.
    Proof.
      Reflexivity.
    Qed.

    Lemma C36 𝐑 𝐒 :
      (forall x, (⊢ 𝐑 x) -> ⊢ 𝐒 x) -> ⊢ ∀ x ⟨𝐑⟩, 𝐒 x.
    Proof.
      Intros H₁ x H₂.
      Apply H₁.
      Assumption.
    Qed.

    Lemma C37 𝐑 𝐒 :
      (forall x, (⊢ 𝐑 x) -> (⊢ ¬𝐒 x) -> Contradiction) -> ⊢ ∀ x ⟨𝐑⟩, 𝐒 x.
    Proof.
      Intros H₁ x H₂ ?contra₁.
      Apply Logic.ex_falso_quodlibet.
      Apply H₁;
        Assumption.
    Qed.

    Lemma C42_iii 𝐑₁ 𝐑₂ 𝐒 :
      ⊢ (∃ x ⟨𝐑₁⟩, ∀ y ⟨𝐑₂⟩, 𝐒 x y) ⇒ ∀ y ⟨𝐑₂⟩, ∃ x ⟨𝐑₁⟩, 𝐒 x y.
    Proof.
      Intros [x H₁] y H₂ [[|]];
        Apply H₁;
        Assumption.
    Qed.
  End Other.
End Other.