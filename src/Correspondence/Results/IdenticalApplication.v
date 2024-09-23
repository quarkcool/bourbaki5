Require Export
  Bourbaki.Correspondence.Correspondence.IdenticalApplication
  Bourbaki.Correspondence.Results.Correspondence
  Bourbaki.Correspondence.Results.Diagonal
  Bourbaki.Correspondence.Results.Graph
  Bourbaki.Correspondence.Results.Meta.GraphComposite
  Bourbaki.Correspondence.Term.Correspondence.

Section IdenticalApplication.
  Context `{Set_.Theory}.

  Theorem composite_leftₑ {X Y} (Γ : Correspondence X Y) :
    ⊢ Id Y ∘ Γ = Γ.
  Proof.
    Apply Graph.equalityₑ.
    Intros x y.
    do 2 (Rewrite CoupleMembershipEquivalenceProof.proof);
      Change (⊢ (∃ y', _) ⇔ _).
    Rewrite (fun _ => Conjunction.commutativity (_ ∈ _)).
    Rewrite <- Conjunction.associativity.
    Rewrite Equality.commutativity.
    Rewrite TypicalExistence.of_equalₑ.
    Apply Conjunction.operand_removal_left.
    Intros H₁.
    Apply (Correspondence.second_projection_subset_essence (G := Γ)).
    Apply MembershipEquivalenceProof.proof.
    Assumption.
  Qed.

  Theorem composite_rightₑ {X Y} (Γ : Correspondence X Y) :
    ⊢ Γ ∘ Id X = Γ.
  Proof.
    Apply Graph.equalityₑ.
    Intros x y.
    do 2 (Rewrite CoupleMembershipEquivalenceProof.proof);
      Change (⊢ (∃ x', _) ⇔ _).
    Rewrite (Conjunction.commutativity (_ ∈ _)).
    Rewrite <- Conjunction.associativity.
    Rewrite Existence.of_equalₑ.
    Apply Conjunction.operand_removal_left.
    Intros H₁.
    Apply (Correspondence.first_projection_subset_essence (G := Γ)).
    Apply MembershipEquivalenceProof.proof.
    Assumption.
  Qed.

  Theorem graphₑ :
    ⊢ ∀ X, Id X = Δ X.
  Proof.
    Rewrite Graph.equalityₑ.
    Intros X x y.
    Rewrite CoupleMembershipEquivalenceProof.proof.
  Qed.
End IdenticalApplication.