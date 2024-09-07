Require Export
  Bourbaki.Equality.Relation.UniqueExistence
  Bourbaki.Equality.Results.Meta.AtMostOneExistence.

Module UniqueExistence.
  Section UniqueExistence.
    Context `{Quantification.Theory, !Equality.Syntax}.

    #[export]
    Instance :
      Morphisms.Proper
        (pointwise_relation _ EquivalenceProof ==> EquivalenceProof)
        unique_existence
    | 1.
    Proof.
      Intros 𝐑 𝐒 H₁.
      unfold unique_existence.
      do 2 (Rewrite H₁).
    Qed.
  End UniqueExistence.
End UniqueExistence.
Export (hints) UniqueExistence.