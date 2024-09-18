Require Export
  Bourbaki.Correspondence.Results.Graph
  Bourbaki.Correspondence.Results.Meta.Product
  Bourbaki.Correspondence.Term.ReverseGraph.

Section ReverseGraph.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall G : Graph, HasGraph (fun x y => ❨y, x❩ ∈ G).
  Proof.
    Intros G.
    Apply GraphPossession.from_container_set.
    Intros [x y H₁].
    Apply (CoupleMembershipEquivalenceProof.proof (pr₂⟨G⟩ × pr₁⟨G⟩)).
    Intros [|];
      Apply MembershipEquivalenceProof.proof;
      Assumption.
  Qed.

  Theorem double_removalₑ G :
    ⊢ G⁻¹⁻¹ = G.
  Proof.
    Apply Graph.equalityₑ.
    Intros x y.
    do 2 (Rewrite CoupleMembershipEquivalenceProof.proof).
  Qed.

  Theorem first_projectionₑ G :
    ⊢ pr₁⟨G⁻¹⟩ = pr₂⟨G⟩.
  Proof.
    Rewrite Set_.equalityₑ.
    Intros y.
    Rewrite MembershipEquivalenceProof.proof;
      Change (⊢ (∃ x, _) ⇔ _).
    Rewrite CoupleMembershipEquivalenceProof.proof.
  Qed.

  Theorem second_projectionₑ G :
    ⊢ pr₂⟨G⁻¹⟩ = pr₁⟨G⟩.
  Proof.
    Rewrite Set_.equalityₑ.
    Intros x.
    Rewrite MembershipEquivalenceProof.proof;
      Change (⊢ (∃ y, _) ⇔ _).
    Rewrite CoupleMembershipEquivalenceProof.proof.
  Qed.
End ReverseGraph.