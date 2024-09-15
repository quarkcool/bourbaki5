Require Export
  Bourbaki.Correspondence.Results.Meta.GraphProjections
  Bourbaki.Correspondence.Results.Meta.RelationGraph
  Bourbaki.Correspondence.Results.Meta.RelationSubgraph
  Bourbaki.Correspondence.Term.Image
  Bourbaki.Correspondence.Term.RelationSubgraph
  Bourbaki.Set.Results.CoupleMembershipEquivalenceProof.

Module Image.
  Section Image.
    Context `{Set_.Theory}.

    #[export]
    Instance :
      forall (G : Graph) X, IsCollectivizing (fun y => ∃ x ⟨∈ X⟩, ❨x, y❩ ∈ G)
    | 0.
    Proof.
      Intros G X [y].
      Rewrite (MembershipEquivalenceProof.proof (pr₂⟨{❨x, _❩ ∈ G | x ∈ X}⟩)).
      Rewrite CoupleMembershipEquivalenceProof.proof.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (InclusionProof ==> InclusionProof ==> InclusionProof)
        image
    | 0.
    Proof.
      Intros G₁ G₂ H₁ X Y H₂ y.
      Rewrite MembershipEquivalenceProof.proof.
      Rewrite H₁.
      Rewrite H₂.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (InclusionProof --> InclusionProof --> Basics.flip InclusionProof)
        image
    | 0 := ltac2:(flip_morphism ()).
  End Image.
End Image.
Export (hints) Image.