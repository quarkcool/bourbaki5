Require Export
  Bourbaki.Correspondence.Results.Meta.GraphPossession
  Bourbaki.Correspondence.Results.Meta.GraphProjections
  Bourbaki.Correspondence.Results.Meta.Product
  Bourbaki.Correspondence.Results.Meta.RelationGraph
  Bourbaki.Correspondence.Term.GraphComposite.

Module GraphComposite.
  Section GraphComposite.
    Context `{Set_.Theory}.

    #[export]
    Instance :
      forall G₁ G₂ : Graph,
        HasGraph (fun x z => ∃ y, ❨x, y❩ ∈ G₂ ∧ ❨y, z❩ ∈ G₁).
    Proof.
      Intros G₁ G₂.
      Apply GraphPossession.from_container_set.
      Intros [x z [y H₃]].
      Apply (CoupleMembershipEquivalenceProof.proof (pr₁⟨G₂⟩ × pr₂⟨G₁⟩)).
      Intros [|];
        Apply MembershipEquivalenceProof.proof;
        Assumption.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (
          InclusionProof (T := Graph_) ==>
          InclusionProof (T := Graph_) ==>
            InclusionProof
        )
        graph_composite
    | 0.
    Proof.
      Intros G₁ G₂ H₁ G₃ G₄ H₂.
      Apply Graph.inclusionₑ.
      Intros x z.
      Rewrite CoupleMembershipEquivalenceProof.proof.
      Rewrite H₁.
      Rewrite H₂.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (
          InclusionProof (T := Graph_) -->
          InclusionProof (T := Graph_) -->
            Basics.flip InclusionProof
        )
        graph_composite
    | 0 := ltac2:(flip_morphism ()).
  End GraphComposite.
End GraphComposite.
Export (hints) GraphComposite.