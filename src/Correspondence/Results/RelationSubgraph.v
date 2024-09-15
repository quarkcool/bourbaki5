Require Export
  Bourbaki.Correspondence.Results.Meta.Graph
  Bourbaki.Correspondence.Results.Meta.RelationGraph
  Bourbaki.Correspondence.Results.Meta.RelationSubgraph
  Bourbaki.Correspondence.Term.RelationSubgraph
  Bourbaki.Set.Results.CoupleMembershipEquivalenceProof.

Section RelationSubgraph.
  Context `{Set_.Theory}.

  Theorem subset_essence 𝐑 :
    ⊢ ∀ G, {❨x, y❩ ∈ G | 𝐑 x y} ⊂ G.
  Proof.
    Rewrite Graph.inclusionₑ.
    Intros G x y.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Apply Conjunction.elimination_right.
  Qed.
End RelationSubgraph.