Require Export
  Bourbaki.Correspondence.Relation.FunctionEssence
  Bourbaki.Correspondence.Results.Correspondence
  Bourbaki.Correspondence.Results.Meta.GraphProjections.

Section FunctionEssence.
  Context `{Set_.Theory}.

  Theorem alternative_definition F :
    ⊢ ∀ X Y,
      is_function F X Y ⇔
        is_correspondence F X Y ∧
          ∀ x ⟨∈ X⟩, unique_existence (fun y => ❨x, y❩ ∈ F).
  Proof.
    Intros X Y.
    Apply Conjunction.conditional_rewriting_right.
    Intros H₁.
    Rewrite (Conjunction.commutativity (is_functional_graph _)).
    Rewrite Set_.equalityₑ₂.
    Rewrite (Conjunction.operand_removal_right (_ ⊂ _)).
    { Change (⊢ (∀ x ⟨_⟩, _) ∧ _ ⇔ _).
      Rewrite (MembershipEquivalenceProof.proof (pr₁⟨F⟩)).
      Rewrite TypicalUniversality.split;
        Change (⊢ _ ⇔ (∀ x ⟨_⟩, ∃ y, _) ∧ _).
      Apply Conjunction.conditional_rewriting_right.
      Intros _ [H₂ x _ | H₂ x y₁ y₂ H₃].
      { Assumption. }
      { Apply H₂.
        { Apply (Correspondence.first_projection_subset_essence (G := F)).
          Apply MembershipEquivalenceProof.proof.
          Assumption. }
        { Assumption. } } }
    { Apply (Correspondence.first_projection_subset_essence (G := F)). }
  Qed.
End FunctionEssence.