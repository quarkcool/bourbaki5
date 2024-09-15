Require Export
  Bourbaki.Correspondence.Results.Meta.GraphPossession.

Section RelationSubgraph.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall 𝐑 X, HasGraph (fun x y => 𝐑 x y ∧ ❨x, y❩ ∈ X).
  Proof.
    Intros 𝐑 X.
    Apply GraphPossession.from_container_set.
    Intros [x y].
    Apply Conjunction.elimination_right.
  Qed.
End RelationSubgraph.