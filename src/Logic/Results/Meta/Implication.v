Require Export
  Bourbaki.Formal.Results.Meta.Implication
  Bourbaki.Logic.Theory.

Module Implication.
  Section Implication.
    Context `{Logic.Theory}.

    #[export]
    Instance :
      forall 𝐀,
        Morphisms.Proper
          (ImplicationProof ==> ImplicationProof)
          (implication 𝐀)
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
          (implication 𝐀)
    | 0 := ltac2:(flip_morphism ()).
  End Implication.
End Implication.
Export (hints) Implication.