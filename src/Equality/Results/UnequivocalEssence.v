Require Export
  Bourbaki.Equality.Relation.UnequivocalEssence
  Bourbaki.Equality.Results.Meta.Equality
  Bourbaki.Meta.Tactic.Change.

Section UnequivocalEssence.
  Context `{Equality.Theory}.

  (* C45_i *)
  Theorem common_term {𝐑} x `(!IsUnequivocal 𝐑) :
    ⊢ 𝐑 x ⇒ x = τ x, 𝐑 x.
  Proof.
    Intros H₁.
    Apply UnequivocalEssence.unequivocal_essence.
    { Assumption. }
    { Rewrite <- Existence.definition.
      Assumption. }
  Qed.

  (* C45_ii *)
  Theorem from_common_term {𝐑 y} :
    (forall x, ⊢ 𝐑 x ⇒ x = y) -> IsUnequivocal 𝐑.
  Proof.
    Intros H₁ x₁ x₂ H₂ H₃.
    Rewrite H₁;
      Assumption.
  Qed.
End UnequivocalEssence.