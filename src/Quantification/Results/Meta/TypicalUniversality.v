Require Export
  Bourbaki.Quantification.Relation.TypicalUniversality
  Bourbaki.Quantification.Results.Meta.Universality.

Module TypicalUniversality.
  Section TypicalUniversality.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    (* C39_ii *)
    #[export]
    Instance :
      forall 𝐑,
        Morphisms.Proper
          (
            forall_relation (fun x => ConditionalImplicationProof (𝐑 x)) ==>
              ImplicationProof
          )
          (typical_universality 𝐑)
    | 0.
    Proof.
      Intros 𝐑 𝐒₁ 𝐒₂ H₁ H₂ x H₃.
      Apply H₁;
        plus [() | Apply H₂];
        Assumption.
    Qed.

    #[export]
    Instance :
      forall 𝐑,
        Morphisms.Proper
          (
            forall_relation (fun x => ConditionalImplicationProof (𝐑 x)) -->
              Basics.flip ImplicationProof
          )
          (typical_universality 𝐑)
    | 0 := ltac2:(flip_morphism ()).

    #[local]
    Instance : Morphisms.Params (@typical_universality) 2 := ltac2:(split).

    (* C39_iv *)
    #[export]
    Instance conditional_rewriting :
      forall 𝐑,
        Morphisms.Proper
          (
            forall_relation (fun x => ConditionalEquivalenceProof (𝐑 x)) ==>
              EquivalenceProof
          )
          (typical_universality 𝐑)
    | 1.
    Proof.
      Intros 𝐑 𝐒₁ 𝐒₂ H₁ [|].
      { Rewrite <- H₁. }
      { Rewrite H₁. }
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (
          pointwise_relation _ ImplicationProof -->
          pointwise_relation _ ImplicationProof ==>
            ImplicationProof
        )
        typical_universality
    | 0.
    Proof.
      Intros 𝐑₂ 𝐑₁ H₁ 𝐒₁ 𝐒₂ H₂; unfold Basics.flip in *.
      unfold typical_universality.
      Rewrite H₁.
      Rewrite H₂.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (
          pointwise_relation _ ImplicationProof ==>
          pointwise_relation _ ImplicationProof -->
            Basics.flip ImplicationProof
        )
        typical_universality
    | 0 := ltac2:(flip_morphism ()).

    #[export]
    Instance :
      Morphisms.Proper
        (
          pointwise_relation _ EquivalenceProof ==>
          pointwise_relation _ EquivalenceProof ==>
            EquivalenceProof
        )
        typical_universality
    | 1.
    Proof.
      Intros 𝐑₁ 𝐑₂ H₁ 𝐒₁ 𝐒₂ H₂.
      unfold typical_universality.
      Rewrite H₁.
      Rewrite H₂.
    Qed.
  End TypicalUniversality.
End TypicalUniversality.
Export (hints) TypicalUniversality.