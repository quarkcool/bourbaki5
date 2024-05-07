Require Export
  Bourbaki.Logic.Results.Meta.Rewriting
  Bourbaki.Quantification.Relation.TypicalExistence
  Bourbaki.Quantification.Relation.TypicalUniversality
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

  (* C39_a *)
  #[export]
  Instance :
    forall 𝐑,
      CMorphisms.Proper
        (
          CMorphisms.forall_relation
            (fun x => ConditionalMetaRelation 𝒯 (𝐑 x) Implication.implication)
          ==>
            ImplicationMetaRelation 𝒯
        )
        (TypicalExistence.typical_existence 𝐑)
      | 0.
  Proof.
    Intros 𝐑 𝐒 𝐓 H₁ [x H₂] [[|]];
      plus [() | Apply H₁];
      Assumption.
  Defined.

  #[export]
  Instance :
    forall 𝐑,
      CMorphisms.Proper
        (
          CMorphisms.forall_relation
            (
              fun x =>
                CRelationClasses.flip
                  (ConditionalMetaRelation 𝒯 (𝐑 x) Implication.implication)
            )
          ==>
            (CRelationClasses.flip (ImplicationMetaRelation 𝒯))
        )
        (TypicalExistence.typical_existence 𝐑)
      | 1.
  Proof.
    assert apply_subrelation by split; typeclasses_eauto.
  Defined.

  (* C39_c *)
  #[export]
  Instance :
    forall 𝐑,
      CMorphisms.Proper
        (
          CMorphisms.forall_relation
            (fun x => ConditionalMetaRelation 𝒯 (𝐑 x) Equivalence.equivalence)
          ==>
            EquivalenceMetaRelation 𝒯
        )
        (TypicalExistence.typical_existence 𝐑)
      | 0.
  Proof.
    Intros 𝐑 𝐒 𝐓 H₁ [|].
    { Rewrite H₁. }
    { Rewrite <- H₁. }
  Defined.

  (* C39_b *)
  #[export]
  Instance :
    forall 𝐑,
      CMorphisms.Proper
        (
          CMorphisms.forall_relation
            (fun x => ConditionalMetaRelation 𝒯 (𝐑 x) Implication.implication)
          ==>
            ImplicationMetaRelation 𝒯
        )
        (TypicalUniversality.typical_universality 𝐑)
      | 0.
  Proof.
    Intros 𝐑 𝐒 𝐓 H₁ H₂ x H₃.
    Apply H₁;
      plus [() | Apply H₂];
      Assumption.
  Defined.

  #[export]
  Instance :
    forall 𝐑,
      CMorphisms.Proper
        (
          CMorphisms.forall_relation
            (
              fun x =>
                CRelationClasses.flip
                  (ConditionalMetaRelation 𝒯 (𝐑 x) Implication.implication)
            )
          ==>
            (CRelationClasses.flip (ImplicationMetaRelation 𝒯))
        )
        (TypicalUniversality.typical_universality 𝐑)
      | 1.
  Proof.
    assert apply_subrelation by split; typeclasses_eauto.
  Defined.

  (* C39_d *)
  #[export]
  Instance :
    forall 𝐑,
      CMorphisms.Proper
        (
          CMorphisms.forall_relation
            (fun x => ConditionalMetaRelation 𝒯 (𝐑 x) Equivalence.equivalence)
          ==>
            EquivalenceMetaRelation 𝒯
        )
        (TypicalUniversality.typical_universality 𝐑)
      | 0.
  Proof.
    Intros 𝐑 𝐒 𝐓 H₁ [|].
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

Section Rewriting.
  Context `(QuantifiedTheory).

  #[export]
  Instance :
    CMorphisms.Proper
      (
        CMorphisms.pointwise_relation _ (EquivalenceMetaRelation 𝒯) ==>
        CMorphisms.pointwise_relation _ (EquivalenceMetaRelation 𝒯) ==>
          EquivalenceMetaRelation 𝒯
      )
      TypicalUniversality.typical_universality
    | 0.
  Proof.
    Intros 𝐑 𝐒 H₁ 𝐓 𝐔 H₂.
    unfold TypicalUniversality.typical_universality.
    Rewrite H₁.
    Rewrite H₂.
  Defined.
End Rewriting.