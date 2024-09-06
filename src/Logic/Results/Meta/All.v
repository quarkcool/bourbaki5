Require Export
  Bourbaki.Logic.Results.Meta.Equivalence.

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

Module Disjunction.
  Section Disjunction.
    Context `{Logic.Theory}.

    #[export]
    Instance :
      Morphisms.Proper
        (EquivalenceProof ==> EquivalenceProof ==> EquivalenceProof)
        disjunction
    | 1.
    Proof.
      Intros 𝐑₁ 𝐒₁ H₁ 𝐑₂ 𝐒₂ H₂ [|].
      { Rewrite <- H₁.
        Rewrite <- H₂. }
      { Rewrite H₁.
        Rewrite H₂. }
    Qed.
  End Disjunction.
End Disjunction.
Export (hints) Disjunction.

Module Negation.
  Section Negation.
    Context `{Logic.Theory}.

    (* C23_i *)
    #[export]
    Instance :
      Morphisms.Proper (EquivalenceProof ==> EquivalenceProof) negation
    | 1.
    Proof.
      Intros 𝐑 𝐒 H₁ [|].
      { Rewrite <- H₁. }
      { Rewrite H₁. }
    Qed.
  End Negation.
End Negation.
Export (hints) Negation.

Module A.
  Module Implication.
    Section Implication.
      Context `{Logic.Theory}.

      #[export]
      Instance :
        Morphisms.Proper
          (EquivalenceProof ==> EquivalenceProof ==> EquivalenceProof)
          implication
      | 1.
      Proof.
        Intros 𝐑₁ 𝐒₁ H₁ 𝐑₂ 𝐒₂ H₂.
        unfold implication.
        Rewrite H₁.
        Rewrite H₂.
      Qed.
    End Implication.
  End Implication.
End A.
Export (hints) A.Implication.

Module Conjunction.
  Section Conjunction.
    Context `{Logic.Theory}.

    #[export]
    Instance :
      Morphisms.Proper
        (EquivalenceProof ==> EquivalenceProof ==> EquivalenceProof)
        conjunction
    | 1.
    Proof.
      Intros 𝐑₁ 𝐒₁ H₁ 𝐑₂ 𝐒₂ H₂.
      unfold conjunction.
      Rewrite H₁.
      Rewrite H₂.
    Qed.
  End Conjunction.
End Conjunction.
Export (hints) Conjunction.

Module Equivalence.
  Section Equivalence.
    Context `{Logic.Theory}.

    #[export]
    Instance :
      Morphisms.Proper
        (EquivalenceProof ==> EquivalenceProof ==> EquivalenceProof)
        Equivalence.equivalence
    | 1.
    Proof.
      Intros 𝐑₁ 𝐒₁ H₁ 𝐑₂ 𝐒₂ H₂.
      unfold Equivalence.equivalence.
      Rewrite H₁.
      Rewrite H₂.
    Qed.
  End Equivalence.
End Equivalence.
Export (hints) Equivalence.