Require Export
  Bourbaki.Correspondence.Relation.GraphPossession
  Bourbaki.Correspondence.Term.RelationGraph
  Bourbaki.Logic.Results.Equivalence
  Bourbaki.Meta.Tactic.Change
  Bourbaki.Quantification.Results.Meta.Universality
  Bourbaki.Set.CoupleMembershipEquivalenceProof.

Section RelationGraph.
  Context `{
    Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory,
    !Equality.Syntax, !Set_.Syntax
  }.

  #[export]
  Instance :
    forall {𝐑},
      HasGraph 𝐑 -> CoupleMembershipEquivalenceProof {❨x, y❩ | 𝐑 x y} 𝐑.
  Proof.
    Intros 𝐑 H₁;
      Change (⊢ ∀ x y, _).
    Rewrite Equivalence.commutativity.
    Apply Conjunction.elimination_right.
    Rewrite <- (Existence.definition (fun G => _ ∧ ∀ _ _, _ ⇔ _ ∈ G)).
    Assumption.
  Qed.

  #[export]
  Instance :
    forall {𝐑}, HasGraph 𝐑 -> IsGraph {❨x, y❩ | 𝐑 x y}.
  Proof.
    Intros 𝐑 H₁.
    Apply Conjunction.elimination_left.
    Rewrite <- (Existence.definition (fun G => is_graph G ∧ _)).
    Assumption.
  Qed.
End RelationGraph.