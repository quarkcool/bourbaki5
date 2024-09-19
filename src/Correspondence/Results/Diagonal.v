Require Export
  Bourbaki.Correspondence.Results.Meta.GraphProjections
  Bourbaki.Correspondence.Term.Diagonal
  Bourbaki.Set.CoupleMembershipEquivalenceProof.

Section Diagonal.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall X, CoupleMembershipEquivalenceProof (Δ X) (fun x y => x ∈ X ∧ y = x).
  Proof.
    Intros X x y.
    Rewrite MembershipEquivalenceProof.proof;
      Change (⊢ (∃ x', _) ⇔ _).
    Rewrite Couple.equalityₑ.
    Rewrite <- (fun _ => Conjunction.commutativity (_ ∈ _)).
    Rewrite (⇑Equality.commutativity x).
    Apply TypicalExistence.of_equalₑ.
  Qed.

  #[export]
  Instance :
    forall X, IsGraph (Δ X).
  Proof.
    Change (forall X, ⊢ ∀ z, _).
    Rewrite MembershipEquivalenceProof.proof.
    Intros X z [x H₁].
    Rewrite H₁.
    Intros [[]].
    Reflexivity.
  Qed.

  Theorem first_projectionₑ :
    ⊢ ∀ X, pr₁⟨Δ X⟩ = X.
  Proof.
    Rewrite Set_.equalityₑ.
    Intros X x.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite (Conjunction.commutativity (_ ∈ _)).
    Apply Existence.of_equalₑ.
  Qed.

  Theorem second_projectionₑ :
    ⊢ ∀ X, pr₂⟨Δ X⟩ = X.
  Proof.
    Rewrite Set_.equalityₑ.
    Intros X y.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite (fun _ => Conjunction.commutativity (_ ∈ _)).
    Rewrite Equality.commutativity.
    Apply Existence.of_equalₑ.
  Qed.
End Diagonal.