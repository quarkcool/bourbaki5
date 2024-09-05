Require Export
  Bourbaki.Logic.Results.Meta.Negation.

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

  (* C9 *)
  Theorem from_consequence {𝐁} 𝐀 :
    (⊢ 𝐁) -> ⊢ 𝐀 ⇒ 𝐁.
  Proof.
    Intros H₁.
    Assumption.
  Qed.
End Implication.