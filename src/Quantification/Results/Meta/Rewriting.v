Require Export
  Bourbaki.Logic.Results.Meta.Rewriting
  Bourbaki.Quantification.Results.Meta.Universality.

Section Rewriting.
  Context `(QuantifiedTheory).

  (* C31_b *)
  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation _ (ImplicationMetaRelation 𝒯) ==>
          ImplicationMetaRelation 𝒯
      )
      Existence.existence
    | 0.
  Proof.
    Intros 𝐑 𝐒 H₁ H₂.
    Apply H₁;
    Assumption.
  Defined.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation
          _ (CRelationClasses.flip (ImplicationMetaRelation 𝒯))
        ==>
          CRelationClasses.flip (ImplicationMetaRelation 𝒯)
      )
      Existence.existence
    | 1.
  Proof.
    assert apply_subrelation by split; typeclasses_eauto.
  Defined.

  (* C31_d *)
  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation _ (EquivalenceMetaRelation 𝒯) ==>
          EquivalenceMetaRelation 𝒯
      )
      Existence.existence
    | 0.
  Proof.
    Intros 𝐑 𝐒 H₁ [|].
    { Rewrite H₁. }
    { Rewrite <- H₁. }
  Defined.

  (* C31_a *)
  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation _ (ImplicationMetaRelation 𝒯) ==>
          ImplicationMetaRelation 𝒯
      )
      Universality.universality
    | 0.
  Proof.
    Intros 𝐑 𝐒 H₁ H₂ x.
    Apply H₁.
    Assumption.
  Defined.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation
          _ (CRelationClasses.flip (ImplicationMetaRelation 𝒯))
        ==>
          CRelationClasses.flip (ImplicationMetaRelation 𝒯)
      )
      Universality.universality
    | 1.
  Proof.
    assert apply_subrelation by split; typeclasses_eauto.
  Defined.

  (* C31_c *)
  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation _ (EquivalenceMetaRelation 𝒯) ==>
          EquivalenceMetaRelation 𝒯
      )
      Universality.universality
    | 0.
  Proof.
    Intros 𝐑 𝐒 H₁ [|].
    { Rewrite H₁. }
    { Rewrite <- H₁. }
  Defined.
End Rewriting.