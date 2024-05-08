Require Export
  Bourbaki.Equality.Relation.FunctionalRelation
  Bourbaki.Equality.Results.Meta.Equality
  Bourbaki.Quantification.Results.Meta.Rewriting.

Section Rewriting.
  Context `(EqualitarianTheory).

  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation _ (EquivalenceMetaRelation 𝒯) ==>
          EquivalenceMetaRelation 𝒯
      )
      AtMostOneExistence.at_most_one_existence
    | 0.
  Proof.
    Intros 𝐑 𝐒 H₁.
    unfold AtMostOneExistence.at_most_one_existence.
    Rewrite H₁.
  Defined.

  #[export]
  Instance :
    forall f,
      CMorphisms.Proper
        (EqualityMetaRelation 𝒯 ==> EqualityMetaRelation 𝒯)
        f
      | 0.
  Proof.
    Intros f x y H₁.
    Apply (Equality.equals_indiscernibility _ _ (fun x => f x = f y)).
    { Assumption. }
    { Reflexivity. }
  Defined.

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

  #[export]
  Instance :
    forall 𝐑,
      CMorphisms.Proper
        (
          EqualityMetaRelation 𝒯 ==> EqualityMetaRelation 𝒯 ==>
            EquivalenceMetaRelation 𝒯
        )
        𝐑
      | 0.
  Proof.
    Intros 𝐑 x y H₁ u v H₂.
    Rewrite H₂.
    Apply (Rewriting.Proper_instance_3 (fun x => 𝐑 x v)).
    Assumption.
  Defined.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation _ (EquivalenceMetaRelation 𝒯) ==>
          EquivalenceMetaRelation 𝒯
      )
      UniqueExistence.unique_existence
    | 0.
  Proof.
    Intros 𝐑 𝐒 H₁.
    unfold UniqueExistence.unique_existence.
    Rewrite H₁.
  Defined.
End Rewriting.

Section Rewriting.
  Context `(EqualitarianTheory).

  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation _ (EquivalenceMetaRelation 𝒯) ==>
          CRelationClasses.flip CRelationClasses.arrow
      )
      (FunctionalRelation 𝒯)
    | 0.
  Proof.
    Intros 𝐑 𝐒 H₁ H₂ 𝒯' H₃.
    Rewrite H₁.
    Apply FunctionalRelation.functional_essence.
  Defined.
End Rewriting.