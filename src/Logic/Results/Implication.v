Require Export
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Logic.Results.Meta.Conjunction.

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

  (* C24_ii *)
  Theorem contrapositiveₑ 𝐑 𝐒 :
    ⊢ 𝐑 ⇒ 𝐒 ⇔ ¬𝐒 ⇒ ¬𝐑.
  Proof.
    Intros [|].
    { Apply Negation.rewriting. }
    { Apply Implication.contrapositive. }
  Qed.

  (* C9 *)
  Theorem from_consequence {𝐒} 𝐑 :
    (⊢ 𝐒) -> ⊢ 𝐑 ⇒ 𝐒.
  Proof.
    Intros H₁.
    Assumption.
  Qed.
End Implication.