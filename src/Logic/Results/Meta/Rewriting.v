Require Export
  Bourbaki.Logic.Results.Meta.Equivalence.

Section Rewriting.
  Context `(LogicalTheory).

  #[export]
  Instance :
    CRelationClasses.subrelation
      (EquivalenceMetaRelation 𝒯)
      (ImplicationMetaRelation 𝒯).
  Proof.
    Intros 𝐀 𝐁 H₁.
    Assumption.
  Defined.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        EquivalenceMetaRelation 𝒯 ==> EquivalenceMetaRelation 𝒯 ==>
          EquivalenceMetaRelation 𝒯
      )
      Formal.disjunction
    | 0.
  Proof.
    Intros 𝐀 𝐁 H₁ 𝐂 𝐃 H₂ [|].
    { Rewrite H₁.
      Rewrite H₂. }
    { Rewrite <- H₁.
      Rewrite <- H₂. }
  Defined.

  (* C23_a *)
  #[export]
  Instance :
    CMorphisms.Proper
      (EquivalenceMetaRelation 𝒯 ==> EquivalenceMetaRelation 𝒯)
      Formal.negation
    | 0.
  Proof.
    Intros 𝐀 𝐁 H₁ [|].
    { Rewrite <- H₁. }
    { Rewrite H₁. }
  Qed.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        EquivalenceMetaRelation 𝒯 ==> EquivalenceMetaRelation 𝒯 ==>
          EquivalenceMetaRelation 𝒯
      )
      Conjunction.conjunction
    | 0.
  Proof.
    Intros 𝐀 𝐁 H₁ 𝐂 𝐃 H₂.
    unfold Conjunction.conjunction.
    Rewrite H₁.
    Rewrite H₂.
  Defined.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        EquivalenceMetaRelation 𝒯 ==> EquivalenceMetaRelation 𝒯 ==>
          EquivalenceMetaRelation 𝒯
      )
      Implication.implication
    | 0.
  Proof.
    Intros 𝐀 𝐁 H₁ 𝐂 𝐃 H₂.
    unfold Implication.implication.
    Rewrite H₁.
    Rewrite H₂.
  Defined.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        EquivalenceMetaRelation 𝒯 ==> EquivalenceMetaRelation 𝒯 ==>
          EquivalenceMetaRelation 𝒯
      )
      Equivalence.equivalence
    | 0.
  Proof.
    Intros 𝐀 𝐁 H₁ 𝐂 𝐃 H₂.
    unfold Equivalence.equivalence.
    Rewrite H₁.
    Rewrite H₂.
  Defined.

  #[export]
  Instance :
    forall {𝒯'} `(𝒯' ⟫ 𝒯),
      CMorphisms.Proper
        (
          EquivalenceMetaRelation 𝒯 ==>
            CRelationClasses.flip CRelationClasses.arrow
        )
        (Proof 𝒯')
      | 0.
  Proof.
    Intros 𝒯' H₁ 𝐀 𝐁 H₂ H₃.
    Apply H₂.
    Assumption.
  Defined.

  #[export]
  Instance :
    forall 𝐀,
      CRelationClasses.subrelation
        (ConditionalMetaRelation 𝒯 𝐀 Equivalence.equivalence)
        (ConditionalMetaRelation 𝒯 𝐀 Implication.implication).
  Proof.
    Intros 𝐀 𝐁 𝐂 H₁ H₂.
    Apply H₁.
    Assumption.
  Defined.

  #[export]
  Instance :
    forall 𝐀,
      CRelationClasses.subrelation
        (ConditionalMetaRelation 𝒯 𝐀 Equivalence.equivalence)
        (CRelationClasses.flip
          (ConditionalMetaRelation 𝒯 𝐀 Implication.implication)).
  Proof.
    Intros 𝐀 𝐁 𝐂 H₁ H₂.
    Apply H₁.
    Assumption.
  Defined.

  #[export]
  Instance :
    CRelationClasses.subrelation
      (EquivalenceMetaRelation 𝒯)
      (CRelationClasses.flip (ImplicationMetaRelation 𝒯)).
  Proof.
    Intros 𝐀 𝐁 H₁; unfold CRelationClasses.flip.
    Assumption.
  Defined.
End Rewriting.