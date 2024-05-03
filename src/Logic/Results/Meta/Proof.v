Require Export
  Bourbaki.Falsity.Theory
  Bourbaki.Logic.Results.Meta.Negation
  Bourbaki.Logic.Theory
  Bourbaki.Meta.Tactic.Change.

Module Implication.
  Section Implication.
    Context `{Logic.CoreTheory}.

    #[export]
    Instance :
      CMorphisms.Proper
        (
          ImplicationMetaRelation ==> ImplicationMetaRelation -->
            CRelationClasses.flip ImplicationMetaRelation
        )
        Implication.implication
      | 0.
    Proof.
      Intros 𝐀 𝐁 H₁ 𝐃 𝐂 H₂; unfold CRelationClasses.flip in *.
      unfold Implication.implication.
      Rewrite H₁.
      Rewrite <- H₂.
    Defined.

    #[export]
    Instance :
      CMorphisms.Proper
        (
          ImplicationMetaRelation --> ImplicationMetaRelation ==>
            ImplicationMetaRelation
        )
        Implication.implication
      | 1.
    Proof.
      assert apply_subrelation by split; typeclasses_eauto.
    Defined.

    Theorem double_condition 𝐀 𝐁 :
      ⊢ (𝐀 ⇒ 𝐀 ⇒ 𝐁) ⇒ 𝐀 ⇒ 𝐁.
    Proof.
      Rewrite (Logic.disjunction_commutativity (¬𝐀)) at 1.
      Rewrite (Logic.disjunction_introduction_left (¬𝐀) 𝐁).
      Apply Logic.disjunction_idempotence.
    Defined.
  End Implication.
End Implication.
Export (hints) Implication.

Section Proof.
  Context `{Logic.Theory}.

  (* méthode de l'hypothèse auxiliaire *)
  Definition auxiliary_hypothesis_introduction_pattern 𝐀 𝐁 :
    IntroductionPattern simple_pattern (⊢ 𝐀 ⇒ 𝐁) :=
  {| Intros.introduction_pattern := Logic.implication_introduction _ _ |}.
End Proof.

Hint Resolve auxiliary_hypothesis_introduction_pattern | 0 :
introduction_pattern_instances.

Section Proof.
  Context `{Logic.Theory}.

  (* méthode de disjonction des cas *)
  Definition case_disjunction_introduction_pattern 𝐀 𝐁 𝐂 :
    IntroductionPattern complex_pattern (⊢ 𝐀 ∨ 𝐁 ⇒ 𝐂).
  Proof.
    refine '{| Intros.NewGoals := (⊢ 𝐀 ⇒ 𝐂) * (⊢ 𝐁 ⇒ 𝐂) |};
      try typeclasses_eauto.
    Intros [H₁ H₂] H₃.
    Apply Disjunction.elimination;
      Assumption.
  Defined.

  (* méthode de réduction à l'absurde *)
  Definition reductio_ad_absurdum_introduction_pattern
    𝐀 (𝐁 : SolveLater Relation) :
      IntroductionPattern fresh_pattern (⊢ 𝐀).
  Proof.
    refine '{| Intros.NewGoals := ⊢ ¬𝐀 -> (⊢ 𝐁) * ⊢ ¬𝐁 |};
      try typeclasses_eauto.
    Intros H₁.
    Apply Logic.disjunction_idempotence.
    Rewrite <- (_ : ¬𝐀 ⊢⇒ 𝐀) at 2.
    { Intros H₂.
      Apply Negation.ex_falso_quodlibet.
      esplit.
      Apply H₁.
      Assumption. }
    { Apply Disjunction.excluded_middle. }
  Defined.
End Proof.

Hint Resolve case_disjunction_introduction_pattern | 0 :
introduction_pattern_instances.

Hint Resolve reductio_ad_absurdum_introduction_pattern | 0 :
introduction_pattern_instances.

Module Negation.
  Section Negation.
    Context `{Falsity.Theory, !Logic.CoreTheory, !Logic.Theory}.

    (* C16 *)
    Theorem doubling 𝐀 :
      ⊢ ¬¬𝐀 ⇒ 𝐀.
    Proof.
      Intros H₁ ?contra₁;
        Assumption.
    Defined.

    Definition entailment {𝐀} (H₁ : SolveLater (⊢ 𝐀)) H₂ :
      Entailment (x := H₂) false (⊢ ¬𝐀) (⊢ ⊥).
    Proof.
      repeat split.
      Apply Negation.ex_falso_quodlibet.
      do 2 esplit;
        Assumption.
    Defined.

    Definition introduction_pattern
      {cat 𝐀} `(pat : IntroductionPattern cat (⊢ 𝐀 ⇒ ⊥)) :
        IntroductionPattern cat (⊢ ¬𝐀).
    Proof.
      refine '{| Intros.NewGoals := Intros.NewGoals |};
        try typeclasses_eauto.
      Intros H₁ ?contra₁.
      { Change (⊢ ⊥);
          try typeclasses_eauto.
        Apply (Intros.introduction_pattern (IntroductionPattern := pat)).
        { Assumption. }
        { Apply Negation.doubling.
          Assumption. } }
      { Apply Falsity.falsity_impossibility. }
    Defined.
  End Negation.

  #[export] Hint Resolve entailment | 3 : entailment_instances.

  #[export]
  Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.
End Negation.
Export (hints) Negation.