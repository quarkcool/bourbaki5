Require Export
  Bourbaki.Logic.Results.Meta.Proof.

Section Implication.
  Context `{Logic.Theory}.

  (* C9 *)
  Theorem from_consequence {𝐁} 𝐀 :
    ⊢ 𝐁 -> ⊢ 𝐀 ⇒ 𝐁.
  Proof.
    Intros H₁.
    Assumption.
  Defined.

  (* C17 *)
  Theorem from_contrapositive 𝐁 𝐀 :
    ⊢ (¬𝐁 ⇒ ¬𝐀) ⇒ 𝐀 ⇒ 𝐁.
  Proof.
    Intros H₁ H₂ ?contra₁.
    { Apply H₂. }
    { Apply H₁.
      Assumption. }
  Defined.
End Implication.