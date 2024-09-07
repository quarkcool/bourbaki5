Require Export
  Bourbaki.Equality.Results.Meta.Equality
  Bourbaki.Logic.Results.Conjunction.

Section Equality.
  Context `{Equality.Theory}.

  Theorem as_conditionₑ x y 𝐑 :
    ⊢ x = y ⇒ 𝐑 x ⇔ x = y ⇒ 𝐑 y.
  Proof.
    Intros [H₁ H₂ | H₁ H₂];
      plus [() | Rewrite <- H₂ | Rewrite H₂];
      Apply H₁;
      Assumption.
  Qed.

  (* C43 *)
  Theorem as_conjunct_leftₑ x y 𝐑 :
    ⊢ x = y ∧ 𝐑 x ⇔ x = y ∧ 𝐑 y.
  Proof.
    Intros [H₁ [|] | H₁ [|]];
      plus [() | Rewrite <- H₁ | Rewrite H₁];
      Assumption.
  Qed.

  Theorem as_conjunct_rightₑ x y 𝐑 :
    ⊢ 𝐑 x ∧ x = y ⇔ 𝐑 y ∧ x = y.
  Proof.
    Rewrite <- (Conjunction.commutativity (_ = _)).
    Apply Equality.as_conjunct_leftₑ.
  Qed.
End Equality.