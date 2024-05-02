Require Export
  Bourbaki.Formal.Results.Meta.Implication
  Bourbaki.Logic.CoreTheory
  Bourbaki.Meta.Tactic.Assumption
  Bourbaki.Meta.Tactic.Intros.

Section Implication.
  Context `{Logic.CoreTheory}.

  #[export]
  Instance :
    forall 𝐀,
      CMorphisms.Proper
        (ImplicationMetaRelation ==> ImplicationMetaRelation)
        (Implication.implication 𝐀)
      | 0.
  Proof.
    Intros 𝐀 𝐁 𝐂 H₁.
    Apply Logic.disjunction_rewriting_right.
    Assumption.
  Defined.

  #[export]
  Instance :
    forall 𝐀,
      CMorphisms.Proper
        (
          ImplicationMetaRelation -->
            CRelationClasses.flip ImplicationMetaRelation
        )
        (Implication.implication 𝐀)
      | 1.
  Proof.
    assert apply_subrelation by split; typeclasses_eauto.
  Defined.
End Implication.