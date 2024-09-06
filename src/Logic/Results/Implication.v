Require Export
  Bourbaki.Logic.Results.Disjunction
  Bourbaki.Logic.Results.Negation.

Section Implication.
  Context `{Logic.Truth.Theory, !Logic.Theory}.

  (* C17 *)
  Theorem contrapositive 𝐁 𝐀 :
    ⊢ (¬𝐁 ⇒ ¬𝐀) ⇒ 𝐀 ⇒ 𝐁.
  Proof.
    Intros H₁ H₂ ?contra₁.
    Apply H₁;
      Assumption.
  Qed.

  (* C24_ii *)
  Theorem contrapositiveₑ 𝐀 𝐁 :
    ⊢ 𝐀 ⇒ 𝐁 ⇔ ¬𝐁 ⇒ ¬𝐀.
  Proof.
    Intros [|].
    { Apply Negation.rewriting. }
    { Apply Implication.contrapositive. }
  Qed.

  (* C9 *)
  Theorem from_consequence {𝐁} 𝐀 :
    (⊢ 𝐁) -> ⊢ 𝐀 ⇒ 𝐁.
  Proof.
    Intros H₁.
    Assumption.
  Qed.

  Theorem with_true_condition 𝐁 𝐀 :
    ⊢ (¬𝐁 ⇒ 𝐀) ⇒ (𝐀 ⇒ 𝐁 ⇔ 𝐁).
  Proof.
    Intros H₁.
    Apply Disjunction.operand_removal_left.
    Apply Implication.contrapositive.
    Rewrite Negation.double_removalₑ.
    Assumption.
  Qed.
End Implication.