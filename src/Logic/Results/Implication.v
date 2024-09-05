Require Export
  Bourbaki.Logic.Results.Meta.Logic.

Section Implication.
  Context `{Logic.Theory}.

  (* C17 *)
  Theorem contrapositive 𝐒 𝐑 :
    ⊢ (¬𝐒 ⇒ ¬𝐑) ⇒ 𝐑 ⇒ 𝐒.
  Proof.
    Intros H₁ H₂ ?contra₁.
    repeat esplit.
    { Apply H₂. }
    { Apply H₁.
      Assumption. }
  Qed.

  (* C9 *)
  Theorem from_consequence {𝐒} 𝐑 :
    (⊢ 𝐒) -> ⊢ 𝐑 ⇒ 𝐒.
  Proof.
    Intros H₁.
    Assumption.
  Qed.
End Implication.