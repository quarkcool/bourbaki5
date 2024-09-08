Require Export
  Bourbaki.Set.Results.Meta.CollectivizingEssence
  Bourbaki.Set.Results.Singleton
  Bourbaki.Set.Term.CollectivizingSubset.

Module CollectivizingSubset.
  Section CollectivizingSubset.
    Context `{Set_.Theory}.

    #[export]
    Instance : Morphisms.Params (@collectivizing_subset) 4 := ltac2:(split).

    (* C51 *)
    #[export]
    Instance :
      forall 𝐑 X, IsCollectivizing (fun x => 𝐑 x ∧ x ∈ X).
    Proof.
      Intros 𝐑 Y.
      Rewrite Conjunction.commutativity.
      Rewrite <- (TypicalExistence.of_equalₑ (fun x => x ∈ Y));
        Change (IsCollectivizing (fun x => ∃ y ⟨_⟩, _)).
      Apply Set_.selection_union.
      Intros y [x H₁].
      Rewrite <- H₁.
      Apply (MembershipEquivalenceProof.proof {y,}).
      Reflexivity.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (
          pointwise_relation _ ImplicationProof ==> InclusionProof ==>
            InclusionProof
        )
        collectivizing_subset
    | 0.
    Proof.
      Intros 𝐑 𝐒 H₁ X Y H₂ x.
      Rewrite MembershipEquivalenceProof.proof.
      Rewrite H₁.
      Rewrite H₂.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (
          pointwise_relation _ ImplicationProof --> InclusionProof -->
            Basics.flip InclusionProof
        )
        collectivizing_subset
    | 0 := ltac2:(flip_morphism ()).
  End CollectivizingSubset.
End CollectivizingSubset.
Export (hints) CollectivizingSubset.