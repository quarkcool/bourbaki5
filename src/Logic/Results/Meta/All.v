Require Export
  Bourbaki.Logic.Results.Meta.Negation.

Module Implication.
  Section Implication.
    Context `{Logic.Theory}.

    (* C13 *)
    Theorem rewriting_left {𝐑 𝐒} 𝐓 :
      (⊢ 𝐑 ⇒ 𝐒) -> ⊢ (𝐒 ⇒ 𝐓) ⇒ 𝐑 ⇒ 𝐓.
    Proof.
      Intros H₁.
      unfold implication at 3.
      Rewrite H₁.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (ImplicationProof ==> ImplicationProof --> Basics.flip ImplicationProof)
        implication
    | 0.
    Proof.
      Intros 𝐑₁ 𝐒₁ H₁ 𝐒₂ 𝐑₂ H₂; unfold Basics.flip, implication in *.
      Rewrite H₁.
      Rewrite <- H₂.
    Qed.
  End Implication.
End Implication.
Export (hints) Implication.