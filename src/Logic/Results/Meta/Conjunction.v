Require Export
  Bourbaki.Logic.Relation.Conjunction
  Bourbaki.Logic.Results.Meta.Proof.

Section Conjunction.
  Context `{Logic.Theory}.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        ImplicationMetaRelation ==> ImplicationMetaRelation ==>
          ImplicationMetaRelation
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
        ImplicationMetaRelation --> ImplicationMetaRelation -->
          CRelationClasses.flip ImplicationMetaRelation
      )
      Conjunction.conjunction
    | 1.
  Proof.
    assert apply_subrelation by split; typeclasses_eauto.
  Defined.

  Theorem contradiction_impossibility 𝐀 :
    ⊢ ¬(𝐀 ∧ ¬𝐀).
  Proof.
    Apply Negation.double_removal.
    Apply Disjunction.excluded_middle.
  Defined.

  (* C21_a *)
  Theorem elimination_left 𝐀 𝐁 :
    ⊢ 𝐀 ∧ 𝐁 ⇒ 𝐀.
  Proof.
    Intros H₁ ?contra₁.
    2: Apply H₁.
    Assumption.
  Defined.

  (* C21_a *)
  Theorem elimination_right 𝐀 𝐁 :
    ⊢ 𝐀 ∧ 𝐁 ⇒ 𝐁.
  Proof.
    Intros H₁ ?contra₁.
    2: Apply H₁.
    Assumption.
  Defined.

  (* C20 *)
  Theorem introduction {𝐀 𝐁} :
    ⊢ 𝐀 -> ⊢ 𝐁 -> ⊢ 𝐀 ∧ 𝐁.
  Proof.
    Intros H₁ H₂ ?contra₁.
    { Apply H₂. }
    { Apply (_ : ⊢ 𝐀 ⇒ ¬𝐁).
      { Apply Negation.doubling.
        Assumption. }
      { Assumption. } }
  Defined.

  Definition introduction_pattern 𝐀 𝐁 :
    IntroductionPattern complex_pattern (⊢ 𝐀 ∧ 𝐁).
  Proof.
    refine '{| Intros.NewGoals := (⊢ 𝐀) * (⊢ 𝐁) |};
      try typeclasses_eauto.
    Intros [H₁ H₂].
    Apply Conjunction.introduction;
      Assumption.
  Defined.

  Definition rewrite_lemma_left
    {𝐀 𝐁} {H₁ : ⊢ 𝐀 ∧ 𝐁} {T}
    `(
        RewriteLemma
          _
          (Formal.syllogism H₁ (Conjunction.elimination_left _ _))
          T
    ) :
      RewriteLemma H₁ T :=
  {| Rewrite.rewrite_lemma := Rewrite.rewrite_lemma |}.

  Definition rewrite_lemma_right
    {𝐀 𝐁} {H₁ : ⊢ 𝐀 ∧ 𝐁} {T}
    `(
        RewriteLemma
          _
          (Formal.syllogism H₁ (Conjunction.elimination_right _ _))
          T
    ) :
      RewriteLemma H₁ T :=
  {| Rewrite.rewrite_lemma := Rewrite.rewrite_lemma |}.
End Conjunction.

#[export]
Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.

#[export]
Hint Resolve rewrite_lemma_left | 2 : rewrite_lemma_instances.

#[export]
Hint Resolve rewrite_lemma_right | 2 : rewrite_lemma_instances.

Section Conjunction.
  Context `{Formal.Syntax}.

  Definition entailment_left
    {𝐀} `(NotEvar _ 𝐀) `{!Formal.Theory, !Logic.CoreTheory, !Logic.Theory}
    {𝐁 H₁ 𝐂}
    `(
      Entailment
        (x := Formal.syllogism H₁ (Conjunction.elimination_left _ _))
        false
        (⊢ 𝐀)
        (⊢ 𝐂)
    ) :
      Entailment (x := H₁) false (⊢ 𝐀 ∧ 𝐁) (⊢ 𝐂).
  Proof.
    repeat split.
    Apply _.
  Defined.

  Definition entailment_right
    {𝐁} `(NotEvar _ 𝐁) `{!Formal.Theory, !Logic.CoreTheory, !Logic.Theory}
    {𝐀 H₁ 𝐂}
    `(
      Entailment
        (x := Formal.syllogism H₁ (Conjunction.elimination_right _ _))
        false
        (⊢ 𝐁)
        (⊢ 𝐂)
    ) :
      Entailment (x := H₁) false (⊢ 𝐀 ∧ 𝐁) (⊢ 𝐂).
  Proof.
    repeat split.
    Apply _.
  Defined.
End Conjunction.

#[export]
Hint Extern 4 (Entailment false _ _) =>
  simple notypeclasses refine (entailment_left _ _) :
entailment_instances.

#[export]
Hint Extern 4 (Entailment false _ _) =>
  simple notypeclasses refine (entailment_right _ _) :
entailment_instances.

Section Conjunction.
  Context `{Logic.Theory}.

  Theorem elimination 𝐀 𝐁 𝐂 :
    ⊢ (𝐀 ⇒ 𝐁 ⇒ 𝐂) ⇒ 𝐀 ∧ 𝐁 ⇒ 𝐂.
  Proof.
    Intros H₁ H₂.
    Apply H₁;
      Assumption.
  Defined.

  Definition destruction_pattern 𝐀 𝐁 𝐂 :
    IntroductionPattern complex_pattern (⊢ 𝐀 ∧ 𝐁 ⇒ 𝐂).
  Proof.
    refine '{| Intros.NewGoals := ⊢ 𝐀 ⇒ 𝐁 ⇒ 𝐂 |};
      try typeclasses_eauto.
    Intros H₁.
    Apply Conjunction.elimination.
    Assumption.
  Defined.

  Theorem symmetry {𝐀 𝐁} :
    ⊢ 𝐀 ∧ 𝐁 -> ⊢ 𝐁 ∧ 𝐀.
  Proof.
    Intros H₁ [|];
      Assumption.
  Defined.
End Conjunction.

#[export]
Hint Resolve destruction_pattern | 0 : introduction_pattern_instances.