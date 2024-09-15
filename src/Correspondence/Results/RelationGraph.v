Require Export
  Bourbaki.Correspondence.Results.Graph.

Section RelationGraph.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall {𝐑} `(!HasGraph 𝐑),
      IsFunctional (fun G => is_graph G ∧ ∀ x y, 𝐑 x y ⇔ ❨x, y❩ ∈ G).
  Proof.
    Intros 𝐑 H₁ [| G₁ G₂ [H₂ H₃] [H₄ H₅]].
    { Assumption. }
    { Apply Graph.equalityₑ.
      Intros x y.
      Rewrite <- H₃.
      Rewrite <- H₅. }
  Qed.

  #[export]
  Instance :
    forall {𝐑} `(!HasGraph 𝐑),
      MembershipEquivalenceProof
        {❨x, y❩ | 𝐑 x y}
        (fun z => ∃ x y, z = ❨x, y❩ ∧ 𝐑 x y).
  Proof.
    Intros 𝐑 H₁ z.
    Rewrite <- (Conjunction.operand_removal_left (z ∈ _) (is_couple z)).
    { Rewrite <- (Existence.of_equal_coupleₑ (fun _ _ => _ ∈ _)).
      Rewrite (fun _ _ => Equality.as_conjunct_leftₑ _ _ (fun z => z ∈ _)).
      Rewrite CoupleMembershipEquivalenceProof.proof. }
    { Apply Graph.graph_essence. }
  Qed.
End RelationGraph.