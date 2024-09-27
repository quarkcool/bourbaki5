Require Export
  Bourbaki.Correspondence.Correspondence.CoordinateFunctions
  Bourbaki.Correspondence.Relation.Surjectivity
  Bourbaki.Correspondence.Results.Injectivity.

Section CoordinateFunctions.
  Context `{Set_.Theory}.

  Theorem injectivity₁ₑ G :
    ⊢ is_injective (coordinate_function₁ G) ⇔ is_functional_graph G.
  Proof.
    Rewrite Injectivity.alternative_definition;
      Change (⊢ (∀ z₁ z₂ ⟨_⟩, _) ⇔ _).
    Rewrite (_ : ∀ z₁ z₂ ⟨∈ G⟩, _ ⊢⇔ ∀ z₁ z₂ ⟨∈ G⟩, pr₁ z₁ = pr₁ z₂ ⇒ z₁ = z₂).
    { Apply TypicalUniversality.conditional_rewriting.
      Intros z₁ H₁.
      Apply TypicalUniversality.conditional_rewriting.
      Intros z₂ H₂.
      Rewrite ValueEqualityProof.proof. }
    { do 2 (Rewrite Graph.typical_universalityₑ);
        Change (⊢ (∀ x₁ y₁, _ ⇒ ∀ x₂ y₂, _) ⇔ _).
      Rewrite CoupleCoordinates.of_couple₁.
      Rewrite Couple.equalityₑ.
      Rewrite Implication.condition_commutativity.
      Rewrite Universality.condition_extraction;
        Change (⊢ (∀ x₁ y₁, _ ⇒ ∀ x₂, _ ⇒ ∀ y₂, _) ⇔ _).
      Rewrite Equality.commutativity at 1.
      Rewrite Universality.over_equalsₑ;
        Change (⊢ (∀ x y₁, _ ⇒ ∀ y₂, _) ⇔ _).
      Rewrite (fun _ _ _ => Conjunction.operand_removal_left _ (_ = _)).
      { Rewrite <- Universality.condition_extraction. }
      { Apply Equality.reflexivity. } }
  Qed.

  Theorem surjectivity₁ G :
    ⊢ is_surjective (coordinate_function₁ G).
  Proof.
    unfold is_surjective.
    Rewrite Image.of_starting_set.
    Rewrite TermFunction.second_projectionₑ.
    Rewrite GraphProjections.alternative_definition₁.
  Qed.

  Theorem surjectivity₂ G :
    ⊢ is_surjective (coordinate_function₂ G).
  Proof.
    unfold is_surjective.
    Rewrite Image.of_starting_set.
    Rewrite TermFunction.second_projectionₑ.
    Rewrite GraphProjections.alternative_definition₂.
  Qed.
End CoordinateFunctions.