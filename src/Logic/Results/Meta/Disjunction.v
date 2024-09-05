Require Export
  Bourbaki.Formal.Results.Meta.Implication
  Bourbaki.Logic.Theory.

Section Disjunction.
  Context `{Logic.Theory}.

  #[export]
  Instance :
    forall 𝐑,
      Morphisms.Proper
        (ImplicationProof --> Basics.flip ImplicationProof)
        (disjunction 𝐑)
  | 0.
  Proof.
    Intros 𝐑 𝐓 𝐒 H₁; unfold Basics.flip in *.
    Apply Logic.disjunction_rewriting_right.
    Assumption.
  Qed.

  Fact entailment_left
    {T 𝐑 𝐒} {x : T} `(NotEvar _ 𝐑) `(Entailment _ true x (⊢ 𝐑)) :
      Entailment true x (⊢ 𝐑 ∨ 𝐒).
  Proof.
    repeat split.
    Apply Logic.disjunction_introduction_left.
    Assumption.
  Defined.
End Disjunction.

Hint Resolve entailment_left | 1 : entailment_instances.