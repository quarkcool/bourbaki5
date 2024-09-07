Require Export
  Bourbaki.Equality.Relation.FunctionalEssence
  Bourbaki.Equality.Results.UnequivocalEssence.

Section FunctionalEssence.
  Context `{Equality.Theory}.

  (* C46_i *)
  Theorem common_term {𝐑} x `(!IsFunctional 𝐑) :
    ⊢ 𝐑 x ⇔ x = τ x, 𝐑 x.
  Proof.
    Intros [|].
    { Apply UnequivocalEssence.common_term.
      Assumption. }
    { Intros H₁.
      Rewrite H₁.
      Rewrite <- Existence.definition.
      Assumption. }
  Qed.

  (* C46_ii *)
  Theorem from_common_term {𝐑 y} :
    (forall x, ⊢ 𝐑 x ⇔ x = y) -> IsFunctional 𝐑.
  Proof.
    Intros H₁ [[] |].
    { Apply H₁.
      Reflexivity. }
    { Apply UnequivocalEssence.from_common_term.
      Intros x.
      Assumption. }
  Qed.
End FunctionalEssence.