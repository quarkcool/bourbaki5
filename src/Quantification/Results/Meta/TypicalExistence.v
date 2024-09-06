Require Export
  Bourbaki.Logic.Results.Meta.All
  Bourbaki.Quantification.Relation.TypicalExistence
  Bourbaki.Quantification.Results.Meta.Existence.

Module TypicalExistence.
  Section TypicalExistence.
    Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

    (* C39_i *)
    #[export]
    Instance :
      forall 𝐑,
        Morphisms.Proper
          (
            forall_relation (fun x => ConditionalImplicationProof (𝐑 x)) ==>
              ImplicationProof
          )
          (typical_existence 𝐑)
    | 0.
    Proof.
      Intros 𝐑 𝐒₁ 𝐒₂ H₁ [x H₂] [[|]];
        plus [() | Apply H₁];
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
          (typical_existence 𝐑)
    | 0 := ltac2:(flip_morphism ()).

    #[local]
    Instance : Morphisms.Params (@typical_existence) 2 := ltac2:(split).

    (* C39_iii *)
    #[export]
    Instance conditional_rewriting :
      forall 𝐑,
        Morphisms.Proper
          (
            forall_relation (fun x => ConditionalEquivalenceProof (𝐑 x)) ==>
              EquivalenceProof
          )
          (typical_existence 𝐑)
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
          pointwise_relation _ ImplicationProof ==>
          pointwise_relation _ ImplicationProof ==>
            ImplicationProof
        )
        typical_existence
    | 0.
    Proof.
      Intros 𝐑₁ 𝐑₂ H₁ 𝐒₁ 𝐒₂ H₂; unfold Basics.flip in *.
      unfold typical_existence.
      Rewrite H₁.
      Rewrite H₂.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (
          pointwise_relation _ ImplicationProof -->
          pointwise_relation _ ImplicationProof -->
            Basics.flip ImplicationProof
        )
        typical_existence
    | 0 := ltac2:(flip_morphism ()).

    #[export]
    Instance :
      Morphisms.Proper
        (
          pointwise_relation _ EquivalenceProof ==>
          pointwise_relation _ EquivalenceProof ==>
            EquivalenceProof
        )
        typical_existence
    | 1.
    Proof.
      Intros 𝐑₁ 𝐑₂ H₁ 𝐒₁ 𝐒₂ H₂.
      unfold typical_existence.
      Rewrite H₁.
      Rewrite H₂.
    Qed.
  End TypicalExistence.
End TypicalExistence.
Export (hints) TypicalExistence.