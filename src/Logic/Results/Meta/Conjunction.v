Require Export
  Bourbaki.Logic.Relation.Conjunction
  Bourbaki.Logic.Results.Meta.Negation.

Module Conjunction.
  Section Conjunction.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    #[export]
    Instance :
      Morphisms.Proper
        (ImplicationProof ==> ImplicationProof ==> ImplicationProof)
        conjunction
    | 0.
    Proof.
      Intros 𝐀₁ 𝐁₁ H₁ 𝐀₂ 𝐁₂ H₂.
      unfold conjunction.
      Rewrite H₁.
      Rewrite H₂.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (ImplicationProof --> ImplicationProof --> Basics.flip ImplicationProof)
        conjunction
    | 0 := ltac2:(flip_morphism ()).

    (* C21_i *)
    Theorem elimination_left 𝐀 𝐁 :
      ⊢ 𝐀 ∧ 𝐁 ⇒ 𝐀.
    Proof.
      Intros H₁ ?contra₁.
      Apply H₁.
      Assumption.
    Qed.

    Fact entailment_left
      {T 𝐀 𝐁} {H₁ : ⊢ 𝐀 ∧ 𝐁}
      `(NotEvar _ 𝐀)
      `(Entailment _ false (Formal.syllogism H₁ (elimination_left _ _)) T) :
        Entailment false H₁ T.
    Proof.
      repeat split.
      Apply _.
    Defined.

    (* C21_ii *)
    Theorem elimination_right 𝐀 𝐁 :
      ⊢ 𝐀 ∧ 𝐁 ⇒ 𝐁.
    Proof.
      Intros H₁ ?contra₁.
      Apply H₁.
      Assumption.
    Qed.

    Fact entailment_right
      {T 𝐀 𝐁} {H₁ : ⊢ 𝐀 ∧ 𝐁}
      `(NotEvar _ 𝐁)
      `(Entailment _ false (Formal.syllogism H₁ (elimination_right _ _)) T) :
        Entailment false H₁ T.
    Proof.
      repeat split.
      Apply _.
    Defined.

    (* C20 *)
    Theorem introduction {𝐀 𝐁} :
      (⊢ 𝐀) -> (⊢ 𝐁) -> ⊢ 𝐀 ∧ 𝐁.
    Proof.
      Intros H₁ H₂ ?contra₁.
      Apply (_ : 𝐀 ⊢⇒ ¬𝐁).
      { Apply Negation.doubling.
        Assumption. }
      all: Assumption.
    Qed.

    Fact introduction_pattern 𝐀 𝐁 :
      IntroductionPattern complex_pattern (⊢ 𝐀 ∧ 𝐁).
    Proof.
      esplit with (NewGoals := (_ * _)%type).
      Intros [H₁ H₂].
      Apply Conjunction.introduction.
      { Apply H₁. }
      { Assumption. }
    Defined.

    Fact rewrite_lemma_left
      {T 𝐀 𝐁} {H₁ : ⊢ 𝐀 ∧ 𝐁}
      `(RewriteLemma (⊢ 𝐀) (Formal.syllogism H₁ (elimination_left _ _)) T) :
        RewriteLemma H₁ T.
    Proof.
      split.
      Apply Rewrite.rewrite_lemma.
    Defined.

    Fact rewrite_lemma_right
      {T 𝐀 𝐁} {H₁ : ⊢ 𝐀 ∧ 𝐁}
      `(RewriteLemma (⊢ 𝐁) (Formal.syllogism H₁ (elimination_right _ _)) T) :
        RewriteLemma H₁ T.
    Proof.
      split.
      Apply Rewrite.rewrite_lemma.
    Defined.
  End Conjunction.

  Hint Resolve entailment_left | 3 : entailment_instances.

  Hint Resolve entailment_right | 3 : entailment_instances.

  Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.

  Hint Resolve rewrite_lemma_left | 2 : rewrite_lemma_instances.

  Hint Resolve rewrite_lemma_right | 2 : rewrite_lemma_instances.

  Section Conjunction.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem elimination 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ⇒ 𝐁 ⇒ 𝐂) ⇒ 𝐀 ∧ 𝐁 ⇒ 𝐂.
    Proof.
      Intros H₁ H₂.
      Apply H₁;
        Assumption.
    Qed.

    Fact destruction_pattern 𝐀 𝐁 𝐂 :
      IntroductionPattern complex_pattern (⊢ 𝐀 ∧ 𝐁 ⇒ 𝐂).
    Proof.
      esplit.
      Intros H₁.
      Apply Conjunction.elimination.
      Assumption.
    Defined.

    Theorem symmetry 𝐀 𝐁 :
      ⊢ 𝐀 ∧ 𝐁 ⇒ 𝐁 ∧ 𝐀.
    Proof.
      Intros H₁ [|];
        Assumption.
    Qed.
  End Conjunction.

  Hint Resolve destruction_pattern | 0 : introduction_pattern_instances.
End Conjunction.
Export (hints) Conjunction.