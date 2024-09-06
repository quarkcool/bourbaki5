Require Export
  Bourbaki.Logic.Results.Negation
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Quantification.Results.Meta.Existence.

Section Universality.
  Context `{Quantification.Theory}.

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
    Rewrite <- H₁.
  Qed.

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
    Apply Negation.double_removalₑ.
  Qed.

  (* C30 *)
  Theorem elimination 𝐑 x :
    ⊢ (∀ x, 𝐑 x) ⇒ 𝐑 x.
  Proof.
    Intros H₁ ?contra₁.
    repeat esplit.
    2: Apply H₁.
    { simpl.
      Assumption. }
  Qed.

  Fact entailment
    {T 𝐑} {H₁ : ⊢ ∀ x, 𝐑 x} {x : SolveLater _}
    `(Entailment
      (⊢ 𝐑 x)
      false
      ltac2:(Apply Universality.elimination; Assumption)
      T
    ) :
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

Hint Resolve entailment | 2 : entailment_instances.

Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.