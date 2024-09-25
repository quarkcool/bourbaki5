Require Export
  Bourbaki.Logic.Results.Meta.All
  Bourbaki.Logic.Results.Negation.

Section Conjunction.
  Context `{Logic.Truth.Theory, !Logic.Theory}.

  (* C24_v *)
  Theorem associativity 𝐀 𝐁 𝐂 :
    ⊢ 𝐀 ∧ 𝐁 ∧ 𝐂 ⇔ (𝐀 ∧ 𝐁) ∧ 𝐂.
  Proof.
    Intros [H₁ [[|] |] | H₁ [| [|]]];
      Assumption.
  Qed.

  (* C24_iv *)
  Theorem commutativity 𝐀 𝐁 :
    ⊢ 𝐀 ∧ 𝐁 ⇔ 𝐁 ∧ 𝐀.
  Proof.
    Intros [|];
      Apply Conjunction.symmetry.
  Qed.

  Theorem operand_removal_right 𝐀 𝐁 :
    ⊢ (𝐀 ⇒ 𝐁) ⇒ (𝐀 ∧ 𝐁 ⇔ 𝐀).
  Proof.
    Intros H₁ [H₂ | H₂ [|]];
      plus [() | Apply H₁];
      Assumption.
  Qed.

  Theorem distributivity_over_conjunction_left 𝐀 𝐁 𝐂 :
    ⊢ 𝐀 ∧ 𝐁 ∧ 𝐂 ⇔ (𝐀 ∧ 𝐁) ∧ 𝐀 ∧ 𝐂.
  Proof.
    Rewrite Conjunction.associativity.
    Rewrite (Conjunction.operand_removal_right _ 𝐀).
    Apply Conjunction.elimination_left.
  Qed.

  (* C24_iii *)
  Theorem idempotenceₑ 𝐀 :
    ⊢ 𝐀 ∧ 𝐀 ⇔ 𝐀.
  Proof.
    Apply Conjunction.operand_removal_right.
    Reflexivity.
  Qed.

  Theorem impossibility 𝐀 :
    ⊢ ¬(𝐀 ∧ ¬𝐀).
  Proof.
    Apply Negation.double_removal.
    Rewrite <- Negation.double_removal.
    Apply Implication.reflexivity.
  Qed.

  Theorem negationₑ 𝐀 𝐁 :
    ⊢ ¬(𝐀 ∧ 𝐁) ⇔ ¬𝐀 ∨ ¬𝐁.
  Proof.
    Apply Negation.double_removalₑ.
  Qed.

  Theorem operand_removal_left 𝐁 𝐀 :
    ⊢ (𝐁 ⇒ 𝐀) ⇒ (𝐀 ∧ 𝐁 ⇔ 𝐁).
  Proof.
    Rewrite (Conjunction.commutativity 𝐀).
    Apply Conjunction.operand_removal_right.
  Qed.
End Conjunction.