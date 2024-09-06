Require Export
  Bourbaki.Logic.Results.All
  Bourbaki.Quantification.Relation.TypicalExistence
  Bourbaki.Quantification.Relation.TypicalUniversality
  Bourbaki.Quantification.Results.Universality.

Module Existence.
  Section Existence.
    Context `{Quantification.Theory}.

    (* C33_ii *)
    Theorem conjunct_extraction_left 𝐑 𝐒 :
      ⊢ (∃ x, 𝐑 ∧ 𝐒 x) ⇔ 𝐑 ∧ ∃ x, 𝐒 x.
    Proof.
      Intros [[x H₁] [|] | [H₁ [x H₂]] [[|]]];
        Assumption.
    Qed.

    (* C29 *)
    Theorem negationₑ 𝐑 :
      ⊢ ¬(∃ x, 𝐑 x) ⇔ ∀ x, ¬𝐑 x.
    Proof.
      unfold universality.
      Rewrite Negation.double_removalₑ at 3.
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

Module Other.
  Section Other.
    Context `{Quantification.Theory}.

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
      Apply H₁;
        Assumption.
    Qed.
  End Other.
End Other.

Module TypicalExistence.
  Section TypicalExistence.
    Context `{Quantification.Theory}.

    (* C38_ii *)
    Theorem negationₑ 𝐑 𝐒 :
      ⊢ ¬(∃ x ⟨𝐑⟩, 𝐒 x) ⇔ ∀ x ⟨𝐑⟩, ¬𝐒 x.
    Proof.
      Rewrite Existence.negationₑ at 1.
      Rewrite Conjunction.negationₑ at 1.
    Qed.
  End TypicalExistence.
End TypicalExistence.

Module TypicalUniversality.
  Section TypicalUniversality.
    Context `{Quantification.Theory}.

    Theorem alternative_definition 𝐑 𝐒 :
      ⊢ (∀ x ⟨𝐑⟩, 𝐒 x) ⇔ ¬∃ x ⟨𝐑⟩, ¬𝐒 x.
    Proof.
      unfold typical_universality, universality.
      Rewrite (fun _ => Implication.negationₑ (𝐑 _)) at 2.
    Qed.

    (* C38_i *)
    Theorem negationₑ 𝐑 𝐒 :
      ⊢ ¬(∀ x ⟨𝐑⟩, 𝐒 x) ⇔ ∃ x ⟨𝐑⟩, ¬𝐒 x.
    Proof.
      Rewrite TypicalUniversality.alternative_definition.
      Apply Negation.double_removalₑ.
    Qed.
  End TypicalUniversality.
End TypicalUniversality.

Module Universality.
  Section Universality.
    Context `{Quantification.Theory}.

    (* C33_i *)
    Theorem disjunct_extraction_left 𝐑 𝐒 :
      ⊢ (∀ x, 𝐑 ∨ 𝐒 x) ⇔ 𝐑 ∨ ∀ x, 𝐒 x.
    Proof.
      Rewrite <- (fun 𝐑 => Negation.double_removalₑ (universality 𝐑)).
      Rewrite Universality.negationₑ.
      Rewrite (Disjunction.negationₑ 𝐑) at 2.
      Rewrite Existence.conjunct_extraction_left.
      Rewrite Conjunction.negationₑ.
      Rewrite Negation.double_removalₑ.
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