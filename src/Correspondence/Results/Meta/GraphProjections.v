Require Export
  Bourbaki.Correspondence.Results.Meta.Graph
  Bourbaki.Correspondence.Term.GraphProjections
  Bourbaki.Set.Results.Meta.CollectivizingSet.

Module GraphProjections.
  Section GraphProjections.
    Context `{Set_.Theory}.

    Theorem membership_equivalenceₑ₁ (G : Graph) :
      ⊢ ∀ x, (∃ y, ❨x, y❩ ∈ G) ⇔ x ∈ set_by_replacement pr₁ G.
    Proof.
      Intros x.
      Rewrite MembershipEquivalenceProof.proof;
        Change (⊢ _ ⇔ ∃ z, _).
      Rewrite (fun _ => Conjunction.commutativity (_ = _)).
      Rewrite Graph.typical_existenceₑ;
        Change (⊢ _ ⇔ ∃ x', _).
      Rewrite <- (fun _ _ => Conjunction.commutativity (_ = _)).
      Rewrite CoupleCoordinates.of_couple₁.
      Rewrite Equality.commutativity.
      Rewrite Existence.conjunct_extraction_left;
        Change (⊢ _ ⇔ ∃ x', _ ∧ ∃ y, _).
      Rewrite Existence.of_equalₑ.
    Qed.

    (* Pr_E_II_3__1_1 *)
    #[export]
    Instance :
      forall {G} `(!IsGraph G), IsCollectivizing (fun x => ∃ y, ❨x, y❩ ∈ G).
    Proof.
      Intros G H₁ [x].
      Rewrite GraphProjections.membership_equivalenceₑ₁.
    Qed.

    Theorem membership_equivalenceₑ₂ (G : Graph) :
      ⊢ ∀ y, (∃ x, ❨x, y❩ ∈ G) ⇔ y ∈ set_by_replacement pr₂ G.
    Proof.
      Intros y.
      Rewrite MembershipEquivalenceProof.proof;
        Change (⊢ _ ⇔ ∃ z, _).
      Rewrite (fun _ => Conjunction.commutativity (_ = _)).
      Rewrite Graph.typical_existenceₑ;
        Change (⊢ _ ⇔ ∃ x y', _).
      Rewrite <- (fun _ _ => Conjunction.commutativity (_ = _)).
      Rewrite CoupleCoordinates.of_couple₂.
      Rewrite Equality.commutativity.
      Rewrite Existence.of_equalₑ.
    Qed.

    (* Pr_E_II_3__1_2 *)
    #[export]
    Instance :
      forall {G} `(!IsGraph G), IsCollectivizing (fun y => ∃ x, ❨x, y❩ ∈ G).
    Proof.
      Intros G H₁ [y].
      Rewrite GraphProjections.membership_equivalenceₑ₂.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper (InclusionProof ==> InclusionProof) first_projection
    | 0.
    Proof.
      Intros G₁ G₂ H₁ x.
      Rewrite MembershipEquivalenceProof.proof.
      Rewrite H₁.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (InclusionProof --> Basics.flip InclusionProof)
        first_projection
    | 0 := ltac2:(flip_morphism ()).

    #[export]
    Instance :
      Morphisms.Proper (InclusionProof ==> InclusionProof) second_projection
    | 0.
    Proof.
      Intros G₁ G₂ H₁ y.
      Rewrite MembershipEquivalenceProof.proof.
      Rewrite H₁.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (InclusionProof --> Basics.flip InclusionProof)
        second_projection
    | 0 := ltac2:(flip_morphism ()).
  End GraphProjections.
End GraphProjections.
Export (hints) GraphProjections.