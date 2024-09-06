Require Export
  Bourbaki.Logic.Results.Conjunction
  Bourbaki.Logic.Results.Implication.

Module Disjunction.
  Section Disjunction.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem as_conditionₑ 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ∨ 𝐁 ⇒ 𝐂 ⇔ (𝐀 ⇒ 𝐂) ∧ (𝐁 ⇒ 𝐂).
    Proof.
      Intros [H₁ [H₂ | H₂] | H₁ [H₂ | H₂]];
        Apply H₁;
        Assumption.
    Qed.

    (* C24_xi *)
    Theorem distributivity_over_conjunction_left 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ∨ 𝐁 ∧ 𝐂 ⇔ (𝐀 ∨ 𝐁) ∧ 𝐀 ∨ 𝐂.
    Proof.
      Intros [[H₁ | H₁] [|] | [[H₁ | H₁] [H₂ | H₂]]];
        plus [() | Apply Conjunction.introduction];
          Assumption.
    Qed.

    Theorem distributivity_over_conjunction_right 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ∧ 𝐁) ∨ 𝐂 ⇔ (𝐀 ∨ 𝐂) ∧ 𝐁 ∨ 𝐂.
    Proof.
      Rewrite <- (Disjunction.commutativity 𝐂).
      Apply Disjunction.distributivity_over_conjunction_left.
    Qed.

    Theorem negationₑ 𝐀 𝐁 :
      ⊢ ¬(𝐀 ∨ 𝐁) ⇔ ¬𝐀 ∧ ¬𝐁.
    Proof.
      unfold conjunction.
      Rewrite Negation.double_removalₑ.
    Qed.
  End Disjunction.
End Disjunction.

Module Conjunction.
  Section Conjunction.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem as_conditionₑ 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ∧ 𝐁 ⇒ 𝐂 ⇔ 𝐀 ⇒ 𝐁 ⇒ 𝐂.
    Proof.
      unfold implication at 1.
      Rewrite Conjunction.negationₑ.
      Rewrite <- Disjunction.associativity.
    Qed.

    Theorem as_consequenceₑ 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ⇒ 𝐁 ∧ 𝐂 ⇔ (𝐀 ⇒ 𝐁) ∧ (𝐀 ⇒ 𝐂).
    Proof.
      Apply Disjunction.distributivity_over_conjunction_left.
    Qed.

    (* C24_x *)
    Theorem distributivity_over_disjunction_left 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ∧ 𝐁 ∨ 𝐂 ⇔ (𝐀 ∧ 𝐁) ∨ 𝐀 ∧ 𝐂.
    Proof.
      Intros [[H₁ [H₂ | H₂]] | [H₁ | H₁] [|]];
        plus [() | Apply Conjunction.introduction];
          Assumption.
    Qed.

    Theorem distributivity_over_disjunction_right 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ∨ 𝐁) ∧ 𝐂 ⇔ (𝐀 ∧ 𝐂) ∨ 𝐁 ∧ 𝐂.
    Proof.
      Rewrite <- (Conjunction.commutativity 𝐂).
      Apply Conjunction.distributivity_over_disjunction_left.
    Qed.
  End Conjunction.
End Conjunction.

Module Implication.
  Section Implication.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem condition_commutativity 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ⇒ 𝐁 ⇒ 𝐂 ⇔ 𝐁 ⇒ 𝐀 ⇒ 𝐂.
    Proof.
      Rewrite <- Conjunction.as_conditionₑ.
      Rewrite (Conjunction.commutativity 𝐀).
    Qed.

    Theorem negationₑ 𝐀 𝐁 :
      ⊢ ¬(𝐀 ⇒ 𝐁) ⇔ 𝐀 ∧ ¬𝐁.
    Proof.
      Rewrite (Disjunction.negationₑ (¬𝐀) 𝐁).
      Rewrite Negation.double_removalₑ.
    Qed.
  End Implication.
End Implication.

Module Negation.
  Section Negation.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem as_conditionₑ 𝐀 𝐁 :
      ⊢ ¬𝐀 ⇒ 𝐁 ⇔ 𝐀 ∨ 𝐁.
    Proof.
      Rewrite <- (Negation.double_removalₑ 𝐀) at 2.
    Qed.
  End Negation.
End Negation.

Module Other.
  Section Other.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Lemma C13 {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇒ 𝐁) -> ⊢ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ⇒ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_ii {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇔ 𝐁) -> ⊢ 𝐀 ⇒ 𝐂 ⇔ 𝐁 ⇒ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_iii {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇔ 𝐁) -> ⊢ 𝐂 ⇒ 𝐀 ⇔ 𝐂 ⇒ 𝐁.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_iv {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇔ 𝐁) -> ⊢ 𝐀 ∧ 𝐂 ⇔ 𝐁 ∧ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_v {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇔ 𝐁) -> ⊢ 𝐀 ∨ 𝐂 ⇔ 𝐁 ∨ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C24_vi 𝐀 𝐁 :
      ⊢ 𝐀 ∨ 𝐁 ⇔ ¬(¬𝐀 ∧ ¬𝐁).
    Proof.
      Rewrite <- Disjunction.negationₑ.
      Rewrite Negation.double_removalₑ.
    Qed.

    Lemma C24_xii 𝐀 𝐁 :
      ⊢ 𝐀 ∧ ¬𝐁 ⇔ ¬(𝐀 ⇒ 𝐁).
    Proof.
      Rewrite (Implication.negationₑ 𝐀 𝐁).
    Qed.

    Lemma C24_xiii 𝐀 𝐁 :
      ⊢ 𝐀 ∨ 𝐁 ⇔ ¬𝐀 ⇒ 𝐁.
    Proof.
      unfold implication.
      Rewrite Negation.double_removalₑ.
    Qed.

    Lemma C25_i {𝐀} 𝐁 :
      (⊢ 𝐀) -> ⊢ 𝐀 ∧ 𝐁 ⇔ 𝐁.
    Proof.
      Intros H₁.
      Apply Conjunction.operand_removal_left.
      Assumption.
    Qed.

    Lemma C25_ii {𝐀} 𝐁 :
      (⊢ ¬𝐀) -> ⊢ 𝐀 ∨ 𝐁 ⇔ 𝐁.
    Proof.
      Intros H₁.
      Apply Disjunction.operand_removal_left.
      Assumption.
    Qed.
  End Other.
End Other.