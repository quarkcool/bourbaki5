Require Export
  Bourbaki.Equality.Relation.AtMostOneExistence
  Bourbaki.Equality.Results.Meta.Truth
  Bourbaki.Quantification.Results.Meta.Universality.

Module AtMostOneExistence.
  Section AtMostOneExistence.
    Context `{Quantification.Theory, !Equality.Syntax}.

    #[export]
    Instance :
      Morphisms.Proper
        (pointwise_relation _ EquivalenceProof ==> EquivalenceProof)
        at_most_one_existence
    | 1.
    Proof.
      Intros 𝐑 𝐒 H₁.
      unfold at_most_one_existence.
      Rewrite H₁.
    Qed.
  End AtMostOneExistence.
End AtMostOneExistence.
Export (hints) AtMostOneExistence.