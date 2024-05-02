Require Export
  Bourbaki.Formal.Results.Meta.Implication
  Bourbaki.Meta.Tactic.Assumption
  Bourbaki.Meta.Tactic.Intros.

Section Proof.
  Context `{Formal.Theory}.

  #[export]
  Instance :
    CMorphisms.Proper
      (ImplicationMetaRelation --> CRelationClasses.flip CRelationClasses.arrow)
      Formal.Proof
    | 0.
  Proof.
    Intros 𝐁 𝐀 H₁ H₂; unfold CRelationClasses.flip in *.
    Apply H₁.
    Assumption.
  Defined.
End Proof.