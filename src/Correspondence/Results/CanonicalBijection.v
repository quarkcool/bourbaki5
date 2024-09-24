Require Export
  Bourbaki.Correspondence.Correspondence.CanonicalBijection
  Bourbaki.Correspondence.Relation.Bijectivity
  Bourbaki.Correspondence.Results.Image
  Bourbaki.Correspondence.Results.Injectivity
  Bourbaki.Correspondence.Results.RelationGraph
  Bourbaki.Correspondence.Results.TermFunction.

Section CanonicalBijection.
  Context `{Set_.Theory}.

  Theorem injectivity G :
    ⊢ is_injective (canonical_bijection G).
  Proof.
    Apply Injectivity.alternative_definition.
    do 2 (Rewrite Graph.typical_universalityₑ);
      Change (⊢ ∀ x₁ y₁, _ ⇒ ∀ x₂ y₂, _).
    Intros x₁ y₁ H₁ x₂ y₂ H₂.
    Rewrite ValueEqualityProof.proof.
    Rewrite CoupleCoordinates.of_couple₂.
    Rewrite CoupleCoordinates.of_couple₁.
    Rewrite Couple.equalityₑ.
    Apply Conjunction.commutativity.
  Qed.

  Theorem surjectivity G :
    ⊢ is_surjective (canonical_bijection G).
  Proof.
    unfold is_surjective.
    Rewrite Image.of_starting_set.
    Rewrite TermFunction.second_projectionₑ.
    Apply Set_.equalityₑ.
    Intros z₁.
    Rewrite MembershipEquivalenceProof.proof;
      Change (⊢ (∃ z₂, _) ⇔ _).
    Rewrite (fun _ => Conjunction.commutativity (_ = ❨_, _❩)).
    Rewrite Graph.typical_existenceₑ.
    Rewrite CoupleCoordinates.of_couple₂.
    Rewrite CoupleCoordinates.of_couple₁.
    Rewrite <- (fun _ _ => Conjunction.commutativity (_ = _)).
    Rewrite Existence.switch at 1.
  Qed.

  Theorem bijectivity G :
    ⊢ is_bijective (canonical_bijection G).
  Proof.
    Intros [|].
    { Apply CanonicalBijection.injectivity. }
    { Apply CanonicalBijection.surjectivity. }
  Qed.
End CanonicalBijection.