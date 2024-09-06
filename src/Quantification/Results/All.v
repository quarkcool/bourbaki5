Require Export
  Bourbaki.Logic.Results.All
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
  End Other.
End Other.

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