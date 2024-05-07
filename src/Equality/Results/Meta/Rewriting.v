Require Export
  Bourbaki.Equality.Meta.EqualityMetaRelation
  Bourbaki.Equality.Theory
  Bourbaki.Logic.Meta.EquivalenceMetaRelation
  Bourbaki.Quantification.Results.Meta.Universality.

Section Rewriting.
  Context `(EqualitarianTheory).

  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation _ (EquivalenceMetaRelation 𝒯) ==>
          EqualityMetaRelation 𝒯
      )
      Formal.tau
    | 0.
  Proof.
    Intros 𝐑 𝐒 H₁.
    Apply Equality.tau_rewriting.
    Intros x.
    Assumption.
  Defined.

  #[export]
  Instance :
    forall 𝐑,
      CMorphisms.Proper
        (EqualityMetaRelation 𝒯 ==> EquivalenceMetaRelation 𝒯)
        𝐑
      | 0.
  Proof.
    Intros 𝐑 x y H₁.
    Apply Equality.equals_indiscernibility.
    Assumption.
  Defined.
End Rewriting.