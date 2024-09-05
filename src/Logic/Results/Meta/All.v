Require Export
  Bourbaki.Logic.Results.Meta.Negation.

Module Implication.
  Section Implication.
    Context `{Logic.Theory}.

    #[export]
    Instance :
      Morphisms.Proper
        (ImplicationProof --> ImplicationProof ==> ImplicationProof)
        implication
    | 0.
    Proof.
      Intros 𝐁₁ 𝐀₁ H₁ 𝐀₂ 𝐁₂ H₂; unfold Basics.flip in *.
      unfold implication.
      Rewrite H₁.
      Rewrite H₂.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (ImplicationProof ==> ImplicationProof --> Basics.flip ImplicationProof)
        implication
    | 0 := ltac2:(flip_morphism ()).
  End Implication.
End Implication.
Export (hints) Implication.