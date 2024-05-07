Require Export
  Bourbaki.Equality.Results.Meta.Equality.

Section Rewriting.
  Context `(EqualitarianTheory).

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
    Apply (Rewriting.Proper_instance_2 (fun x => 𝐑 x v)).
    Assumption.
  Defined.
End Rewriting.