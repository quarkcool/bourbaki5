Require Export
  Bourbaki.Correspondence.Correspondence.TermFunction
  Bourbaki.Correspondence.Results.ReverseGraph.

Section CanonicalBijection.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall G : Graph, set_by_replacement (fun z => ❨pr₂ z, pr₁ z❩) G ⊢⊂ G⁻¹.
  Proof.
    Change (forall G, ⊢ ∀ z₁, _).
    Rewrite MembershipEquivalenceProof.proof.
    Intros G z₁ [z₂ H₁].
    Rewrite H₁.
    Apply CoupleMembershipEquivalenceProof.proof.
    Rewrite <- CoupleEssence.alternative_definition;
      plus [() | Apply Graph.graph_essence];
      Assumption.
  Qed.

  (* bijection canonique  *)
  Definition canonical_bijection (G : Graph) :
    G → G⁻¹ :=
  z ∈ G ↦ ❨pr₂ z, pr₁ z❩ ∈ G⁻¹.
End CanonicalBijection.