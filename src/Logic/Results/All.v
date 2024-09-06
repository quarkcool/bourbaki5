Require Export
  Bourbaki.Logic.Results.Conjunction
  Bourbaki.Logic.Results.Disjunction
  Bourbaki.Logic.Results.Implication.

Module Conjunction.
  Section Conjunction.
    Context `{Logic.Theory}.

    (* C24_x *)
    Theorem distributivity_over_conjunction_left 𝐑 𝐒 𝐓 :
      ⊢ 𝐑 ∧ (𝐒 ∨ 𝐓) ⇔ 𝐑 ∧ 𝐒 ∨ (𝐑 ∧ 𝐓).
    Proof.
      Intros [[H₁ [H₂ | H₂]] | [H₁ | H₁] [|]];
        plus [() | Apply Conjunction.introduction];
          Assumption.
    Qed.
  End Conjunction.
End Conjunction.

Module Disjunction.
  Section Disjunction.
    Context `{Logic.Theory}.

    (* C24_xi *)
    Theorem distributivity_over_conjunction_left 𝐑 𝐒 𝐓 :
      ⊢ 𝐑 ∨ (𝐒 ∧ 𝐓) ⇔ 𝐑 ∨ 𝐒 ∧ (𝐑 ∨ 𝐓).
    Proof.
      Intros [[H₁ | H₁] [|] | [[H₁ | H₁] [H₂ | H₂]]];
        plus [() | Apply Conjunction.introduction];
          Assumption.
    Qed.

    Theorem negationₑ 𝐑 𝐒 :
      ⊢ ¬(𝐑 ∨ 𝐒) ⇔ ¬𝐑 ∧ ¬𝐒.
    Proof.
      unfold conjunction.
      Rewrite Negation.double_removalₑ.
    Qed.
  End Disjunction.
End Disjunction.

Module Implication.
  Section Implication.
    Context `{Logic.Theory}.

    Theorem negationₑ 𝐑 𝐒 :
      ⊢ ¬(𝐑 ⇒ 𝐒) ⇔ 𝐑 ∧ ¬𝐒.
    Proof.
      Rewrite (Disjunction.negationₑ (¬𝐑) 𝐒).
      Rewrite Negation.double_removalₑ.
    Qed.
  End Implication.
End Implication.

Module Other.
  Section Other.
    Context `{Logic.Theory}.

    Lemma C23_ii {𝐀 𝐁} 𝐂 :
      (𝐀 ⊢⇔ 𝐁) -> ⊢ 𝐀 ⇒ 𝐂 ⇔ 𝐁 ⇒ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_iii {𝐀 𝐁} 𝐂 :
      (𝐀 ⊢⇔ 𝐁) -> ⊢ 𝐂 ⇒ 𝐀 ⇔ 𝐂 ⇒ 𝐁.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_iv {𝐀 𝐁} 𝐂 :
      (𝐀 ⊢⇔ 𝐁) -> ⊢ 𝐀 ∧ 𝐂 ⇔ 𝐁 ∧ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_v {𝐀 𝐁} 𝐂 :
      (𝐀 ⊢⇔ 𝐁) -> ⊢ 𝐀 ∨ 𝐂 ⇔ 𝐁 ∨ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C24_v 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ∧ (𝐁 ∧ 𝐂) ⇔ 𝐀 ∧ 𝐁 ∧ 𝐂.
    Proof.
      Rewrite Conjunction.associativity.
    Qed.

    Lemma C24_vi 𝐀 𝐁 :
      ⊢ 𝐀 ∨ 𝐁 ⇔ ¬(¬𝐀 ∧ ¬𝐁).
    Proof.
      Rewrite <- Disjunction.negationₑ.
      Rewrite Negation.double_removalₑ.
    Qed.

    Lemma C24_ix 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ∨ (𝐁 ∨ 𝐂) ⇔ 𝐀 ∨ 𝐁 ∨ 𝐂.
    Proof.
      Rewrite Disjunction.associativity.
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