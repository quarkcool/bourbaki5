Require Export
  Bourbaki.Logic.Results.Meta.Implication
  Bourbaki.Meta.Tactic.Destruct.

Module Disjunction.
  Section Disjunction.
    Context `{Logic.Theory}.

    #[export]
    Instance :
      Morphisms.Proper
        (ImplicationProof ==> ImplicationProof ==> ImplicationProof)
        disjunction
    | 0.
    Proof.
      Intros 𝐀₁ 𝐁₁ H₁ 𝐀₂ 𝐁₂ H₂.
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

    #[export]
    Instance :
      Morphisms.Proper
        (ImplicationProof --> ImplicationProof --> Basics.flip ImplicationProof)
        disjunction
    | 0 := ltac2:(flip_morphism ()).

    Fact destructible 𝐀 𝐁 :
      Destructible (⊢ 𝐀 ∨ 𝐁).
    Proof.
      repeat split.
    Defined.

    (* C18 *)
    Theorem elimination {𝐀 𝐁 𝐂} :
      (⊢ 𝐀 ∨ 𝐁) -> (⊢ 𝐀 ⇒ 𝐂) -> (⊢ 𝐁 ⇒ 𝐂) -> ⊢ 𝐂.
    Proof.
      Intros H₁ H₂ H₃.
      Apply Logic.disjunction_idempotence.
      Rewrite <- H₂ at 1.
      Rewrite <- H₃.
      Assumption.
    Qed.

    Fact destruction_pattern 𝐀 𝐁 𝐂 :
      IntroductionPattern complex_pattern (⊢ 𝐀 ∨ 𝐁 ⇒ 𝐂).
    Proof.
      esplit with (NewGoals := (_ * _)%type).
      Intros [H₁ H₂] H₃.
      Apply Disjunction.elimination.
      { Assumption. }
      { Apply H₁. }
      { Assumption. }
    Defined.

    Fact entailment_left
      {T 𝐀 𝐁} {x : T} `(NotEvar _ 𝐀) `(Entailment _ true x (⊢ 𝐀)) :
        Entailment true x (⊢ 𝐀 ∨ 𝐁).
    Proof.
      repeat split.
      Apply Logic.disjunction_introduction_left.
      Assumption.
    Defined.

    (* C7 *)
    Theorem introduction_right 𝐁 𝐀 :
      ⊢ 𝐁 ⇒ 𝐀 ∨ 𝐁.
    Proof.
      Rewrite <- (Logic.disjunction_symmetry 𝐁).
      Apply Logic.disjunction_introduction_left.
    Qed.

    Fact entailment_right
      {T 𝐁 𝐀} {x : T} `(NotEvar _ 𝐁) `(Entailment _ true x (⊢ 𝐁)) :
        Entailment true x (⊢ 𝐀 ∨ 𝐁).
    Proof.
      repeat split.
      Apply Disjunction.introduction_right.
      Assumption.
    Defined.
  End Disjunction.

  Hint Resolve destructible | 0 : destructible_instances.

  Hint Resolve entailment_left | 1 : entailment_instances.

  Hint Resolve entailment_right | 1 : entailment_instances.

  Hint Resolve destruction_pattern | 0 : introduction_pattern_instances.
End Disjunction.
Export (hints) Disjunction.