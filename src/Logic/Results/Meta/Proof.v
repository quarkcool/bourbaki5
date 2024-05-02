Require Export
  Bourbaki.Logic.Results.Meta.Negation.

Module Implication.
  Section Implication.
    Context `{Logic.CoreTheory}.

    #[export]
    Instance :
      CMorphisms.Proper
        (
          ImplicationMetaRelation ==> ImplicationMetaRelation -->
            CRelationClasses.flip ImplicationMetaRelation
        )
        Implication.implication
      | 0.
    Proof.
      Intros 𝐀 𝐁 H₁ 𝐃 𝐂 H₂; unfold CRelationClasses.flip in *.
      unfold Implication.implication.
      Rewrite H₁.
      Rewrite <- H₂.
    Defined.

    #[export]
    Instance :
      CMorphisms.Proper
        (
          ImplicationMetaRelation --> ImplicationMetaRelation ==>
            ImplicationMetaRelation
        )
        Implication.implication
      | 1.
    Proof.
      assert apply_subrelation by split; typeclasses_eauto.
    Defined.
  End Implication.
End Implication.
Export (hints) Implication.