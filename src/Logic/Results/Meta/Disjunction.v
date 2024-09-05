Require Export
  Bourbaki.Formal.Results.Meta.Implication
  Bourbaki.Logic.Theory
  Bourbaki.Meta.Tactic.Destruct.

Module Disjunction.
  Section Disjunction.
    Context `{Logic.Theory}.

    #[export]
    Instance :
      forall 𝐀,
        Morphisms.Proper
          (ImplicationProof ==> ImplicationProof)
          (disjunction 𝐀)
    | 0.
    Proof.
      Intros 𝐀 𝐁 𝐂 H₁.
      Apply Logic.disjunction_rewriting_right.
      Assumption.
    Qed.

    #[export]
    Instance :
      forall 𝐀,
        Morphisms.Proper
          (ImplicationProof --> Basics.flip ImplicationProof)
          (disjunction 𝐀)
    | 0 := ltac2:(flip_morphism ()).

    Fact destructible 𝐀 𝐁 :
      Destructible (⊢ 𝐀 ∨ 𝐁).
    Proof.
      repeat split.
    Defined.

    Fact entailment_left
      {T 𝐀 𝐁} {x : T} `(NotEvar _ 𝐀) `(Entailment _ true x (⊢ 𝐀)) :
        Entailment true x (⊢ 𝐀 ∨ 𝐁).
    Proof.
      repeat split.
      Apply Logic.disjunction_introduction_left.
      Assumption.
    Defined.
  End Disjunction.

  Hint Resolve destructible | 0 : destructible_instances.

  Hint Resolve entailment_left | 1 : entailment_instances.
End Disjunction.
Export (hints) Disjunction.