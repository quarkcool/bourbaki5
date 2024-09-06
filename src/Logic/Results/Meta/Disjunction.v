Require Export
  Bourbaki.Logic.Results.Meta.Implication.

Section Disjunction.
  Context `{Logic.Theory}.

  #[export]
  Instance :
    Morphisms.Proper
      (ImplicationProof --> ImplicationProof --> Basics.flip ImplicationProof)
      disjunction
  | 0.
  Proof.
    Intros 𝐒₁ 𝐑₁ H₁ 𝐒₂ 𝐑₂ H₂; unfold Basics.flip in *.
    Transitivity.
    { Apply Logic.disjunction_rewriting_right.
      Assumption. }
    { Transitivity.
      { Apply Logic.disjunction_symmetry. }
      { Transitivity.
        { Apply Logic.disjunction_rewriting_right.
          Assumption. }
        { Apply Logic.disjunction_symmetry. } } }
  Qed.

  (* C18 *)
  Theorem elimination {𝐑 𝐒 𝐓} :
    (⊢ 𝐑 ∨ 𝐒) -> (⊢ 𝐑 ⇒ 𝐓) -> (⊢ 𝐒 ⇒ 𝐓) -> ⊢ 𝐓.
  Proof.
    Intros H₁ H₂ H₃.
    Apply Logic.disjunction_idempotence.
    Rewrite <- H₂ at 1.
    Rewrite <- H₃.
    Assumption.
  Qed.

  Fact destruction_pattern 𝐑 𝐒 𝐓 :
    IntroductionPattern complex_pattern (⊢ 𝐑 ∨ 𝐒 ⇒ 𝐓).
  Proof.
    esplit with (NewGoals := (_ * _)%type).
    Intros [H₁ H₂] H₃.
    Apply Disjunction.elimination.
    { Assumption. }
    { Apply H₁. }
    { Assumption. }
  Defined.

  Fact entailment_left
    {T 𝐑 𝐒} {x : T} `(NotEvar _ 𝐑) `(Entailment _ true x (⊢ 𝐑)) :
      Entailment true x (⊢ 𝐑 ∨ 𝐒).
  Proof.
    repeat split.
    Apply Logic.disjunction_introduction_left.
    Assumption.
  Defined.

  (* C7 *)
  Theorem introduction_right 𝐒 𝐑 :
    ⊢ 𝐒 ⇒ 𝐑 ∨ 𝐒.
  Proof.
    Transitivity.
    { Apply (Logic.disjunction_introduction_left _ 𝐑). }
    { Apply Logic.disjunction_symmetry. }
  Qed.

  Fact entailment_right
    {T 𝐒 𝐑} {x : T} `(NotEvar _ 𝐒) `(Entailment _ true x (⊢ 𝐒)) :
      Entailment true x (⊢ 𝐑 ∨ 𝐒).
  Proof.
    repeat split.
    Apply Disjunction.introduction_right.
    Assumption.
  Defined.
End Disjunction.

Hint Resolve entailment_left | 1 : entailment_instances.

Hint Resolve entailment_right | 1 : entailment_instances.

Hint Resolve destruction_pattern | 0 : introduction_pattern_instances.