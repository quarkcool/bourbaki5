Require Export
  Bourbaki.Logic.Results.All
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

Module Other.
  Section Other.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    Lemma C34_iii 𝐑 :
      ⊢ (∃ x, ∀ y, 𝐑 x y) ⇒ ∀ y, ∃ x, 𝐑 x y.
    Proof.
      Intros [x H₁] y.
      Assumption.
    Qed.
  End Other.
End Other.