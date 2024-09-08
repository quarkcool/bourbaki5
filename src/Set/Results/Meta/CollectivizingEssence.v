Require Export
  Bourbaki.Equality.Results.Meta.Truth
  Bourbaki.Quantification.Results.Meta.Universality
  Bourbaki.Set.Relation.CollectivizingEssence.

Module CollectivizingEssence.
  Section CollectivizingEssence.
    Context `{Quantification.Theory, !Equality.Syntax, !Set_.Syntax}.

    #[export]
    Instance :
      Morphisms.Proper
        (pointwise_relation _ EquivalenceProof ==> EquivalenceProof)
        Coll
    | 1.
    Proof.
      Intros 𝐑 𝐒 H₁.
      unfold Coll.
      Rewrite H₁.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (pointwise_relation _ EquivalenceProof ==> Basics.flip Basics.impl)
        IsCollectivizing
    | 1.
    Proof.
      Intros 𝐑 𝐒 H₁ H₂.
      unfold IsCollectivizing.
      Rewrite H₁.
      Assumption.
    Qed.
  End CollectivizingEssence.
End CollectivizingEssence.
Export (hints) CollectivizingEssence.