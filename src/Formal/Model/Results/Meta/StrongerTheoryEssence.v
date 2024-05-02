Require Export
  Bourbaki.Formal.Model.Meta.StrongerTheoryEssence
  Bourbaki.Formal.Model.Results.CanonicalModel
  Bourbaki.Formal.Model.Results.Meta.Proof
  Bourbaki.Formal.Results.Meta.Implication
  Bourbaki.Meta.Tactic.Revert
  Bourbaki.Util.Results.Set.

Section StrongerTheoryEssence.
  Context `{Formal.Syntax}.

  #[export]
  Instance from_inclusions :
    forall
      {𝒯₁ 𝒯₂}
      `(
        𝒯₁.(ExplicitAxioms) ⊂ 𝒯₂.(ExplicitAxioms),
        𝒯₁.(Schemas) ⊂ 𝒯₂.(Schemas)
      ),
        𝒯₂ ⊃ 𝒯₁ | 3.
  Proof.
    Intros 𝒯₁ 𝒯₂ H₁ H₂.
    split.
    { Intros 𝐀 H₃.
      Apply Proof.explicit_axiom.
      Apply H₁.
      Assumption. }
    { Assumption. }
  Defined.

  #[export]
  Instance reflexivity :
    forall 𝒯, 𝒯 ⊃ 𝒯 | 2.
  Proof.
    Intros 𝒯.
    typeclasses_eauto.
  Defined.

  #[export]
  Instance :
    CRelationClasses.Reflexive StrongerTheoryEssence.
  Proof.
    Apply StrongerTheoryEssence.reflexivity.
  Defined.

  (* C4 *)
  Theorem weaker_theorem {𝒯₂ 𝒯₁} `(𝒯₂ ⊃ 𝒯₁) {𝐀} :
    𝒯₁ ⊢ 𝐀 -> 𝒯₂ ⊢ 𝐀.
  Proof.
    Intros H₁.
    induction H₁ as [𝐀 H₁ | 𝐀 H₁ | 𝐀 𝐁 _ IH₁ _ IH₂].
    { Apply StrongerTheoryEssence.weaker_explicit_axiom.
      Assumption. }
    { Apply StrongerTheoryEssence.weaker_schema.
      Assumption. }
    { Apply IH₂; simpl.
      Assumption. }
  Defined.

  Definition entailment
    {𝒯₁ 𝒯₂} `(Ununifiable 𝒯₁ 𝒯₂) `{𝒯₂ ⊃ 𝒯₁} {𝐀 H₁ 𝐁}
    `(
      Entailment
        (x := StrongerTheoryEssence.weaker_theorem _ H₁)
        false
        (𝒯₂ ⊢ 𝐀)
        (𝒯₂ ⊢ 𝐁)
    ) :
      Entailment (x := H₁) false (𝒯₁ ⊢ 𝐀) (𝒯₂ ⊢ 𝐁).
  Proof.
    repeat split.
    Apply _.
  Defined.

  Definition rewrite_lemma {𝒯₂ 𝒯₁} (H₁ : 𝒯₂ ⊃ 𝒯₁) :
    RewriteLemma H₁ (𝒯₂ ⊃ 𝒯₁) :=
  {| Rewrite.rewrite_lemma := H₁ |}.
End StrongerTheoryEssence.

Hint Extern 2 (Entailment false _ _) =>
  simple notypeclasses refine (entailment _ _) :
entailment_instances.

Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.

Module Implication.
  Section Implication.
    Context `{Formal.Syntax}.

    Definition revert {𝒯₂ 𝒯₁} `(𝒯₂ ⊃ 𝒯₁) {𝐀} (H₁ : 𝒯₁ ⊢ 𝐀) 𝐁 :
      Revert H₁ (𝒯₂ ⊢ 𝐁).
    Proof.
      refine '{| Revert.NewGoals := 𝒯₂ ⊢ 𝐀 ⇒ 𝐁 |}.
      Intros H₂.
      Apply H₂; simpl.
      Assumption.
    Defined.
  End Implication.

  Hint Resolve revert | 0 : revert_instances.
End Implication.
Export (hints) Implication.

Module Proof.
  Section Proof.
    Context `{Formal.Syntax}.

    #[export]
    Instance :
      CMorphisms.Proper
        (
          StrongerTheoryEssence ==> Logic.eq ==>
            CRelationClasses.flip CRelationClasses.arrow
        )
        Proof
      | 0.
    Proof.
      Intros 𝒯₂ 𝒯₁ H₁ 𝐀 𝐁 H₂ H₃.
      rewrite H₂.
      Assumption.
    Defined.

    #[export]
    Instance :
      forall 𝒯,
        CMorphisms.Proper
          (
            ImplicationMetaRelation -->
              CRelationClasses.flip CRelationClasses.arrow
          )
          (Proof 𝒯)
        | 0.
    Proof.
      Intros 𝒯 𝐁 𝐀 H₁ H₂; unfold CRelationClasses.flip in *.
      Apply H₁; simpl.
      Assumption.
    Defined.
  End Proof.
End Proof.
Export (hints) Proof.

Section StrongerTheoryEssence.
  Context `{Formal.Syntax}.

  #[export]
  Instance transitivity :
    CRelationClasses.Transitive StrongerTheoryEssence.
  Proof.
    Intros 𝒯₃ 𝒯₂ 𝒯₁ H₁ H₂.
    split.
    { Intros 𝐀 H₃.
      Rewrite H₁.
      Assumption. }
    { Intros 𝐀 H₃.
      do 2 (Apply StrongerTheoryEssence.weaker_schema).
      Assumption. }
  Defined.
End StrongerTheoryEssence.

Hint Extern 5 (?𝒯₂ ⊃ ?𝒯₁) =>
  let cstr := uconstr:(transitivity 𝒯₂ _ 𝒯₁ _ _) in
  notypeclasses refine cstr; [| eassumption] :
typeclass_instances.