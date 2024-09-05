Require Export
  Bourbaki.Logic.Relation.Conjunction
  Bourbaki.Logic.Results.Meta.Negation.

Section Conjunction.
  Context `{Logic.Theory}.

  #[export]
  Instance :
    Morphisms.Proper
      (ImplicationProof --> ImplicationProof --> Basics.flip ImplicationProof)
      conjunction
  | 0.
  Proof.
    Intros 𝐒₁ 𝐑₁ H₁ 𝐒₂ 𝐑₂ H₂; unfold Basics.flip, conjunction in *.
    Rewrite H₁.
    Rewrite H₂.
  Qed.

  (* C21_i *)
  Theorem elimination_left 𝐑 𝐒 :
    ⊢ 𝐑 ∧ 𝐒 ⇒ 𝐑.
  Proof.
    Intros H₁ ?contra₁.
    repeat esplit.
    2: Apply H₁.
    { Assumption. }
  Qed.

  Fact entailment_left
    {T 𝐑 𝐒} {H₁ : ⊢ 𝐑 ∧ 𝐒}
    `(NotEvar _ 𝐑)
    `(Entailment
      (T₁ := ⊢ 𝐑)
      false
      ltac2:(Apply Conjunction.elimination_left; Assumption)
      T
    ) :
      Entailment false H₁ T.
  Proof.
    repeat split.
    Apply _.
  Defined.

  (* C21_ii *)
  Theorem elimination_right 𝐑 𝐒 :
    ⊢ 𝐑 ∧ 𝐒 ⇒ 𝐒.
  Proof.
    Intros H₁ ?contra₁.
    repeat esplit.
    2: Apply H₁.
    { Assumption. }
  Qed.

  Fact entailment_right
    {T 𝐑 𝐒} {H₁ : ⊢ 𝐑 ∧ 𝐒}
    `(NotEvar _ 𝐒)
    `(Entailment
      (T₁ := ⊢ 𝐒)
      false
      ltac2:(Apply Conjunction.elimination_right; Assumption)
      T
    ) :
      Entailment false H₁ T.
  Proof.
    repeat split.
    Apply _.
  Defined.

  (* C20 *)
  Theorem introduction {𝐑 𝐒} :
    (⊢ 𝐑) -> (⊢ 𝐒) -> ⊢ 𝐑 ∧ 𝐒.
  Proof.
    Intros H₁ H₂ ?contra₁.
    repeat esplit.
    { Apply H₂. }
    { Apply (_ : 𝐑 ⊢⇒ ¬𝐒).
      { Apply Negation.doubling.
        Assumption. }
      { Assumption. } }
  Qed.

  Fact introduction_pattern 𝐑 𝐒 :
    IntroductionPattern complex_pattern (⊢ 𝐑 ∧ 𝐒).
  Proof.
    esplit with (NewGoals := (_ * _)%type).
    Intros [H₁ H₂].
    Apply Conjunction.introduction.
    { Apply H₁. }
    { Assumption. }
  Defined.
End Conjunction.

Hint Resolve entailment_left | 3 : entailment_instances.

Hint Resolve entailment_right | 3 : entailment_instances.

Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.

Section Conjunction.
  Context `{Logic.Theory}.

  Theorem elimination 𝐑 𝐒 𝐓 :
    ⊢ (𝐑 ⇒ 𝐒 ⇒ 𝐓) ⇒ 𝐑 ∧ 𝐒 ⇒ 𝐓.
  Proof.
    Intros H₁ H₂.
    Apply H₁;
      Assumption.
  Qed.

  Fact destruction_pattern 𝐑 𝐒 𝐓 :
    IntroductionPattern complex_pattern (⊢ 𝐑 ∧ 𝐒 ⇒ 𝐓).
  Proof.
    esplit.
    Intros H₁.
    Apply Conjunction.elimination.
    Assumption.
  Defined.

  Theorem symmetry 𝐑 𝐒 :
    ⊢ 𝐑 ∧ 𝐒 ⇒ 𝐒 ∧ 𝐑.
  Proof.
    Intros H₁ [|];
      Assumption.
  Qed.
End Conjunction.

Hint Resolve destruction_pattern | 0 : introduction_pattern_instances.