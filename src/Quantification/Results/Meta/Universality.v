Require Export
  Bourbaki.Logic.Results.Meta.All
  Bourbaki.Logic.Results.Negation
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Quantification.Results.Meta.Existence.

Module Universality.
  Section Universality.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    (* C31_i *)
    #[export]
    Instance :
      Morphisms.Proper
        (pointwise_relation _ ImplicationProof ==> ImplicationProof)
        universality
    | 0.
    Proof.
      Intros 𝐑 𝐒 H₁.
      unfold universality.
      Rewrite H₁.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (pointwise_relation _ ImplicationProof --> Basics.flip ImplicationProof)
        universality
    | 0 := ltac2:(flip_morphism ()).

    (* C31_iii *)
    #[export]
    Instance :
      Morphisms.Proper
        (pointwise_relation _ EquivalenceProof ==> EquivalenceProof)
        universality
    | 1.
    Proof.
      Intros 𝐑 𝐒 H₁.
      unfold universality.
      Rewrite H₁.
    Qed.

    (* C26 *)
    Theorem alternative_definition 𝐑 :
      ⊢ (∀ x, 𝐑 x) ⇔ 𝐑 (τ x, ¬𝐑 x).
    Proof.
      unfold universality.
      Rewrite Existence.definition.
      Apply Negation.double_removalₑ.
    Qed.

    (* C30 *)
    Theorem elimination 𝐑 x :
      ⊢ (∀ x, 𝐑 x) ⇒ 𝐑 x.
    Proof.
      Intros H₁ ?contra₁.
      Apply H₁.
      Assumption.
    Qed.

    Fact entailment
      {T 𝐑} {H₁ : ⊢ ∀ x, 𝐑 x} {x : SolveLater _}
      `(Entailment (⊢ 𝐑 x) false (Formal.syllogism H₁ (elimination _ _)) T) :
        Entailment false H₁ T.
    Proof.
      repeat split.
      Apply _.
    Defined.

    (* C27 *)
    Theorem introduction 𝐑 :
      (forall x, ⊢ 𝐑 x) -> ⊢ ∀ x, 𝐑 x.
    Proof.
      Intros H₁.
      Apply Universality.alternative_definition.
      Assumption.
    Qed.

    Fact introduction_pattern 𝐑 :
      IntroductionPattern simple_pattern (⊢ ∀ x, 𝐑 x).
    Proof.
      esplit.
      Apply Universality.introduction.
    Defined.
  End Universality.

  Notation "⇑ H₁" :=
    (fun x => Formal.syllogism H₁ (elimination _ x)) :
  bourbaki_scope.

  Hint Resolve entailment | 2 : entailment_instances.

  Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.

  Section Universality.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    Fact rewrite_lemma
      {TT 𝐑} {H₁ : ⊢ ∀ x, 𝐑 x}
      `(lem : forall x, @RewriteLemma (⊢ 𝐑 x) (⇑H₁ x) (TT x)) :
        RewriteLemma H₁ (forall x, TT x).
    Proof.
      split.
      Intros x.
      Apply Rewrite.rewrite_lemma.
    Defined.
  End Universality.

  Hint Resolve rewrite_lemma | 2 : rewrite_lemma_instances.
End Universality.
Export (hints, notations) Universality.