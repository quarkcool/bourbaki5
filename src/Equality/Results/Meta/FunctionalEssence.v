Require Export
  Bourbaki.Equality.Relation.FunctionalEssence
  Bourbaki.Equality.Results.Meta.UniqueExistence.

Module FunctionalEssence.
  Section FunctionalEssence.
    Context `{Quantification.Theory, !Equality.Syntax}.

    (* Ex_E_I_5__4 *)
    #[export]
    Instance :
      Morphisms.Proper
        (pointwise_relation _ EquivalenceProof ==> Basics.flip Basics.impl)
        IsFunctional.
    Proof.
      Intros 𝐑 𝐒 H₁ H₂.
      unfold IsFunctional.
      Rewrite H₁.
      Assumption.
    Qed.
  End FunctionalEssence.
End FunctionalEssence.
Export (hints) FunctionalEssence.