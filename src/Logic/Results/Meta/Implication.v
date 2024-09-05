Require Export
  Bourbaki.Formal.Results.Meta.Implication
  Bourbaki.Logic.Theory
  Coq.Setoids.Setoid.

Section Implication.
  Context `{Logic.Theory}.

  #[export]
  Instance :
    forall 𝐑,
      Morphisms.Proper
        (ImplicationProof --> Basics.flip ImplicationProof)
        (implication 𝐑)
  | 0.
  Proof.
    Intros 𝐑 𝐓 𝐒 H₁; unfold Basics.flip in *.
    Apply Logic.disjunction_rewriting_right.
    Assumption.
  Qed.

  (* C6 *)
  Theorem transitivity {𝐑 𝐒 𝐓} :
    (⊢ 𝐑 ⇒ 𝐒) -> (⊢ 𝐒 ⇒ 𝐓) -> ⊢ 𝐑 ⇒ 𝐓.
  Proof.
    Intros H₁ H₂.
    Rewrite <- H₂.
    Assumption.
  Qed.

  #[export]
  Instance :
    Transitive ImplicationProof.
  Proof.
    Apply @Implication.transitivity.
  Qed.

  (* C8 *)
  Theorem reflexivity 𝐑 :
    ⊢ 𝐑 ⇒ 𝐑.
  Proof.
    Transitivity.
    { Apply (Logic.disjunction_introduction_left _ 𝐑). }
    { Apply Logic.disjunction_idempotence. }
  Qed.

  #[export]
  Instance :
    Reflexive ImplicationProof.
  Proof.
    Apply Implication.reflexivity.
  Qed.

  Fact introduction_pattern 𝐑 𝐒 :
    IntroductionPattern simple_pattern (⊢ 𝐑 ⇒ 𝐒).
  Proof.
    esplit.
    Apply Logic.deduction.
  Defined.
End Implication.

Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.