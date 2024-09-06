Require Export
  Bourbaki.Logic.Results.Meta.Equivalence.

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

Module Disjunction.
  Section Disjunction.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    #[export]
    Instance :
      Morphisms.Proper
        (EquivalenceProof ==> EquivalenceProof ==> EquivalenceProof)
        disjunction
    | 1.
    Proof.
      Intros 𝐀₁ 𝐁₁ H₁ 𝐀₂ 𝐁₂ H₂ [|].
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
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    (* C23_i *)
    #[export]
    Instance :
      Morphisms.Proper (EquivalenceProof ==> EquivalenceProof) negation
    | 1.
    Proof.
      Intros 𝐀 𝐁 H₁ [|].
      { Rewrite <- H₁. }
      { Rewrite H₁. }
    Qed.
  End Negation.
End Negation.
Export (hints) Negation.

Module A.
  Module Implication.
    Section Implication.
      Context `{Logic.Truth.Theory, !Logic.Theory}.

      #[export]
      Instance :
        Morphisms.Proper
          (EquivalenceProof ==> EquivalenceProof ==> EquivalenceProof)
          implication
      | 1.
      Proof.
        Intros 𝐀₁ 𝐁₁ H₁ 𝐀₂ 𝐁₂ H₂.
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
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    #[export]
    Instance conditional_rewriting_right :
      forall 𝐀,
        Morphisms.Proper
          (ConditionalEquivalenceProof 𝐀 ==> EquivalenceProof)
          (conjunction 𝐀)
    | 1.
    Proof.
      Intros 𝐀 𝐁 𝐂 H₁ [H₂ [|] | H₂ [|]];
        plus [() | Apply H₁];
          Assumption.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (EquivalenceProof ==> EquivalenceProof ==> EquivalenceProof)
        conjunction
    | 1.
    Proof.
      Intros 𝐀₁ 𝐁₁ H₁ 𝐀₂ 𝐁₂ H₂.
      unfold conjunction.
      Rewrite H₁.
      Rewrite H₂.
    Qed.
  End Conjunction.
End Conjunction.
Export (hints) Conjunction.

Module Equivalence.
  Section Equivalence.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    #[export]
    Instance :
      Morphisms.Proper
        (EquivalenceProof ==> EquivalenceProof ==> EquivalenceProof)
        Equivalence.equivalence
    | 1.
    Proof.
      Intros 𝐀₁ 𝐁₁ H₁ 𝐀₂ 𝐁₂ H₂.
      unfold Equivalence.equivalence.
      Rewrite H₁.
      Rewrite H₂.
    Qed.
  End Equivalence.
End Equivalence.
Export (hints) Equivalence.