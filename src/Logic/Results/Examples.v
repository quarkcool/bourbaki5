Require Export
  Bourbaki.Logic.Results.All.

Import Proof.TheoryHidingNotation.

Section Examples.
  Context `{Logic.CoreTheory}.

  Example C13 {𝐀 𝐁} 𝐂 :
    ⊢ 𝐀 ⇒ 𝐁 -> ⊢ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ⇒ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C23_b {𝐀 𝐁} 𝐂 :
    𝐀 ⊢⟨𝒯⟩⇔ 𝐁 -> 𝒯 ⊢ 𝐀 ⇒ 𝐂 ⇔ 𝐁 ⇒ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C23_c {𝐀 𝐁} 𝐂 :
    𝐀 ⊢⟨𝒯⟩⇔ 𝐁 -> 𝒯 ⊢ 𝐂 ⇒ 𝐀 ⇔ 𝐂 ⇒ 𝐁.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C23_d {𝐀 𝐁} 𝐂 :
    𝐀 ⊢⟨𝒯⟩⇔ 𝐁 -> 𝒯 ⊢ 𝐀 ∧ 𝐂 ⇔ 𝐁 ∧ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C23_e {𝐀 𝐁} 𝐂 :
    𝐀 ⊢⟨𝒯⟩⇔ 𝐁 -> 𝒯 ⊢ 𝐀 ∨ 𝐂 ⇔ 𝐁 ∨ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C24_e 𝐀 𝐁 𝐂 :
    𝒯 ⊢ 𝐀 ∧ (𝐁 ∧ 𝐂) ⇔ 𝐀 ∧ 𝐁 ∧ 𝐂.
  Proof.
    Rewrite Conjunction.associativity.
  Defined.

  Example C24_f 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∨ 𝐁 ⇔ ¬(¬𝐀 ∧ ¬𝐁).
  Proof.
    Rewrite <- (Negation.double_removal _ (_ ∨ _)).
    Rewrite (Disjunction.negationₑ _ 𝐀).
  Defined.

  Example C24_i 𝐀 𝐁 𝐂 :
    𝒯 ⊢ 𝐀 ∨ (𝐁 ∨ 𝐂) ⇔ 𝐀 ∨ 𝐁 ∨ 𝐂.
  Proof.
    Rewrite Disjunction.associativity.
  Defined.

  Example C24_l 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∧ ¬𝐁 ⇔ ¬(𝐀 ⇒ 𝐁).
  Proof.
    Rewrite (Implication.negationₑ _ _ 𝐁).
  Defined.

  Example C24_m 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∨ 𝐁 ⇔ ¬𝐀 ⇒ 𝐁.
  Proof.
    unfold Implication.implication.
    Rewrite Negation.double_removal.
  Defined.

  Example C25_a 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 -> 𝒯 ⊢ 𝐀 ∧ 𝐁 ⇔ 𝐁.
  Proof.
    Intros H₁.
    Apply Conjunction.operand_removal_leftₑ.
    Assumption.
  Defined.

  Example C25_b 𝐀 𝐁 :
    𝒯 ⊢ ¬𝐀 -> 𝒯 ⊢ 𝐀 ∨ 𝐁 ⇔ 𝐁.
  Proof.
    Intros H₁.
    Apply Disjunction.operand_removal_leftₑ.
    Assumption.
  Defined.

  Example EX_I_3_1_a 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ⇒ 𝐁 ⇒ 𝐀.
  Proof.
    Intros H₁ _.
    Assumption.
  Defined.

  Example EX_I_3_1_b 𝐀 𝐁 𝐂 :
    𝒯 ⊢ (𝐀 ⇒ 𝐁) ⇒ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ⇒ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example EX_I_3_1_c 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ⇒ ¬𝐀 ⇒ 𝐁.
  Proof.
    Intros H₁ H₂.
    Apply Negation.ex_falso_quodlibet.
    do 2 esplit;
      Assumption.
  Defined.

  Example EX_I_3_1_d 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∨ 𝐁 ⇔ (𝐀 ⇒ 𝐁) ⇒ 𝐁.
  Proof.
    unfold Implication.implication at 1.
    Rewrite (Implication.negationₑ _ 𝐀).
    Rewrite Disjunction.distributivity_with_conjunction_right.
    Rewrite (Conjunction.operand_removal_rightₑ _ (𝐀 ∨ 𝐁)).
    Intros _.
    Apply Disjunction.commutativity.
    Apply Disjunction.excluded_middle.
  Defined.

  Example EX_I_3_1_e 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ⇔ 𝐁 ⇔ 𝐀 ∧ 𝐁 ∨ (¬𝐀 ∧ ¬𝐁).
  Proof.
    Rewrite Disjunction.distributivity_with_conjunction_left.
    Rewrite Disjunction.distributivity_with_conjunction_right.
    Rewrite (Conjunction.operand_removal_leftₑ _ (𝐀 ∨ ¬𝐀)).
    { Rewrite (Conjunction.operand_removal_rightₑ _ _ (𝐁 ∨ ¬𝐁)).
      { Rewrite Disjunction.commutativity. }
      { Apply Disjunction.excluded_middle. } }
    { Apply Disjunction.excluded_middle. }
  Defined.

  Example EX_I_3_1_f 𝐀 𝐁 :
    𝒯 ⊢ ¬(¬𝐀 ⇔ 𝐁) ⇒ (𝐀 ⇔ 𝐁).
  Proof.
    Rewrite (Examples.EX_I_3_1_e (¬𝐀)).
    Rewrite (Disjunction.negationₑ _ (_ ∧ _)).
    Rewrite Conjunction.negationₑ.
    Rewrite Negation.double_removal.
    Rewrite (Disjunction.commutativity _ 𝐀).
    Apply Conjunction.commutativity.
  Defined.

  Example EX_I_3_1_g 𝐀 𝐁 𝐂 :
    𝒯 ⊢ 𝐀 ⇒ 𝐁 ∨ ¬𝐂 ⇔ 𝐂 ∧ 𝐀 ⇒ 𝐁.
  Proof.
    Rewrite <- Disjunction.associativity.
    Rewrite (Disjunction.commutativity _ (_ ∨ _)).
    Rewrite <- Disjunction.associativity.
    Rewrite <- Conjunction.negationₑ.
  Defined.

  Example EX_I_3_1_h 𝐀 𝐁 𝐂 :
    𝒯 ⊢ 𝐀 ⇒ 𝐁 ∨ 𝐂 ⇔ 𝐁 ∨ (𝐀 ⇒ 𝐂).
  Proof.
    Rewrite <- Disjunction.associativity.
    Rewrite (Disjunction.commutativity _ (¬𝐀)).
  Defined.

  Example EX_I_3_1_i 𝐀 𝐁 𝐂 :
    𝒯 ⊢ (𝐀 ⇒ 𝐁) ⇒ (𝐀 ⇒ 𝐂) ⇒ 𝐀 ⇒ 𝐁 ∧ 𝐂.
  Proof.
    Rewrite <- Conjunction.as_conditionₑ.
    Apply Conjunction.as_consequenceₑ.
  Defined.

  Example EX_I_3_1_j 𝐀 𝐂 𝐁 :
    𝒯 ⊢ (𝐀 ⇒ 𝐂) ⇒ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ∨ 𝐁 ⇒ 𝐂.
  Proof.
    Rewrite <- Conjunction.as_conditionₑ.
    Apply Disjunction.as_conditionₑ.
  Defined.

  Example EX_I_3_1_k 𝐀 𝐁 𝐂 :
    𝒯 ⊢ (𝐀 ⇒ 𝐁) ⇒ 𝐀 ∧ 𝐂 ⇒ 𝐁 ∧ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example EX_I_3_1_l 𝐀 𝐁 𝐂 :
    𝒯 ⊢ (𝐀 ⇒ 𝐁) ⇒ 𝐀 ∨ 𝐂 ⇒ 𝐁 ∨ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example EX_I_3_2 {𝐀} :
    (𝒯 ⊢ 𝐀 ⇔ ¬𝐀) -> Contradictory 𝒯.
  Proof.
    Intros H₁.
    do 2 esplit.
    { Assumption. }
    { Apply Equivalence.fundamental_impossibility. }
  Defined.

  Section EX_I_3_4.
    Definition alternative_denial 𝐀 𝐁 := ¬𝐀 ∨ ¬𝐁.

    Infix "|" :=
      alternative_denial (at level 72, left associativity) :
    bourbaki_scope.

    Example EX_I_3_4_a 𝐀 :
      𝒯 ⊢ ¬𝐀 ⇔ 𝐀 | 𝐀.
    Proof.
      Rewrite Disjunction.idempotence.
    Defined.

    Example EX_I_3_4_b 𝐀 𝐁 :
      𝒯 ⊢ 𝐀 ∨ 𝐁 ⇔ 𝐀 | 𝐀 | (𝐁 | 𝐁).
    Proof.
      unfold alternative_denial at 1.
      Rewrite <- EX_I_3_4.EX_I_3_4_a.
      Rewrite Negation.double_removal.
    Defined.

    Example EX_I_3_4_c 𝐀 𝐁 :
      𝒯 ⊢ 𝐀 ∧ 𝐁 ⇔ 𝐀 | 𝐁 | (𝐀 | 𝐁).
    Proof.
      Apply EX_I_3_4.EX_I_3_4_a.
    Defined.

    Example EX_I_3_4_d 𝐀 𝐁 :
      𝒯 ⊢ 𝐀 ⇒ 𝐁 ⇔ 𝐀 | (𝐁 | 𝐁).
    Proof.
      unfold alternative_denial at 1.
      Rewrite <- EX_I_3_4.EX_I_3_4_a.
      Rewrite Negation.double_removal.
    Defined.
  End EX_I_3_4.
End Examples.