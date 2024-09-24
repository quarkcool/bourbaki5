Require Export
  Bourbaki.Correspondence.Correspondence.ReverseCorrespondence
  Bourbaki.Correspondence.Relation.Bijectivity
  Bourbaki.Correspondence.Results.Image
  Bourbaki.Correspondence.Results.Injectivity.

Section ReverseApplication.
  Context `{Set_.Theory}.

  Theorem functional_graph_essenceₑ {X Y} (f : X → Y) :
    ⊢ is_functional_graph f⁻¹ ⇔ is_injective f.
  Proof.
    Change (⊢ (∀ y x₁ x₂, _) ⇔ _).
    do 2 (Rewrite CoupleMembershipEquivalenceProof.proof).
    do 2 (Rewrite Conjunction.as_conditionₑ).
    Rewrite Universality.switch; Rewrite Universality.switch at 2;
      Change (⊢ (∀ x₁ x₂ y, _) ⇔ _).
    Rewrite TypicalUniversality.over_equalsₑ.
    Rewrite Universality.condition_extraction;
      Change (⊢ (∀ x₁ x₂ ⟨_⟩, _) ⇔ _).
    Rewrite <- Injectivity.alternative_definition.
  Qed.

  (* Pr_E_II_3__7 *)
  Theorem function_essenceₑ {X Y} (f : X → Y) :
    ⊢ is_function f⁻¹ Y X ⇔ is_bijective f.
  Proof.
    Change (⊢ _ ∧ _ ⇔ _).
    Rewrite (Conjunction.operand_removal_left _ (is_correspondence _ _ _)).
    { Rewrite ReverseApplication.functional_graph_essenceₑ.
      Rewrite ReverseGraph.first_projectionₑ.
      Rewrite <- Image.of_starting_set.
      Rewrite Equality.commutativity. }
    { Apply Correspondence.correspondence_essence. }
  Qed.

  #[export]
  Instance :
    forall {X Y} (f : X → Y) `(!IsBijective f), IsFunction f⁻¹ Y X.
  Proof.
    Intros X Y f H₁.
    Apply ReverseApplication.function_essenceₑ.
    Assumption.
  Qed.

  (* application réciproque de f *)
  Definition reverse_application {X Y} (f : X → Y) `(!IsBijective f) :
    Y → X :=
  f⁻¹.
End ReverseApplication.