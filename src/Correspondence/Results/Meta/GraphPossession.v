Require Export
  Bourbaki.Correspondence.Relation.GraphPossession
  Bourbaki.Set.Results.All.

Section GraphPossession.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    Morphisms.Proper
      (
        pointwise_relation _ (pointwise_relation _ EquivalenceProof) ==>
          EquivalenceProof
      )
      has_graph.
  Proof.
    Intros 𝐑₁ 𝐑₂ H₁.
    unfold has_graph.
    Rewrite H₁.
  Qed.

  #[export]
  Instance :
    Morphisms.Proper
      (
        pointwise_relation _ (pointwise_relation _ EquivalenceProof) ==>
          Basics.flip Basics.impl
      )
      HasGraph.
  Proof.
    Intros 𝐑₁ 𝐑₂ H₁ H₂.
    unfold HasGraph.
    Rewrite H₁.
    Assumption.
  Qed.

  Theorem from_container_set 𝐑 :
    (⊢ ∃ X, ∀ x y, 𝐑 x y ⇒ ❨x, y❩ ∈ X) -> ⊢ has_graph 𝐑.
  Proof.
    Intros [X H₁] [];
      Change (⊢ (∀ z, _) ∧ _).
    Rewrite (
      MembershipEquivalenceProof.proof {z ∈ X | ∃ x y, z = ❨x, y❩ ∧ 𝐑 x y}
    );
      Change (⊢ _ ∧ ∀ x y, _ ⇔ (∃ x' y', _) ∧ _).
    Intros [z [[x [y H₂]] _] | x y].
    { Rewrite H₂.
      Apply Couple.couple_essence. }
    { Rewrite Existence.of_equal_coupleₑ₂.
      Rewrite (Conjunction.operand_removal_right (𝐑 _ _)).
      Assumption. }
  Qed.
End GraphPossession.