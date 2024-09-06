Require Export
  Bourbaki.Logic.Results.Meta.All
  Bourbaki.Logic.Results.Negation.

Section Conjunction.
  Context `{Logic.Theory}.

  Theorem associativity 𝐑 𝐒 𝐓 :
    ⊢ 𝐑 ∧ 𝐒 ∧ 𝐓 ⇔ 𝐑 ∧ (𝐒 ∧ 𝐓).
  Proof.
    Intros [H₁ [| [|]] | H₁ [[|] |]];
      Assumption.
  Qed.

  (* C24_iv *)
  Theorem commutativity 𝐑 𝐒 :
    ⊢ 𝐑 ∧ 𝐒 ⇔ 𝐒 ∧ 𝐑.
  Proof.
    Intros [|];
      Apply Conjunction.symmetry.
  Qed.

  Theorem negationₑ 𝐑 𝐒 :
    ⊢ ¬(𝐑 ∧ 𝐒) ⇔ ¬𝐑 ∨ ¬𝐒.
  Proof.
    Apply Negation.double_removalₑ.
  Qed.

  Theorem operand_removal_right 𝐑 𝐒 :
    ⊢ (𝐑 ⇒ 𝐒) ⇒ (𝐑 ∧ 𝐒 ⇔ 𝐑).
  Proof.
    Intros H₁ [H₂ | H₂ [|]];
      plus [() | Apply H₁];
      Assumption.
  Qed.

  (* C24_iii *)
  Theorem idempotenceₑ 𝐑 :
    ⊢ 𝐑 ∧ 𝐑 ⇔ 𝐑.
  Proof.
    Apply Conjunction.operand_removal_right.
    Reflexivity.
  Qed.

  Theorem operand_removal_left 𝐒 𝐑 :
    ⊢ (𝐒 ⇒ 𝐑) ⇒ (𝐑 ∧ 𝐒 ⇔ 𝐒).
  Proof.
    Rewrite (Conjunction.commutativity 𝐑).
    Apply Conjunction.operand_removal_right.
  Qed.
End Conjunction.