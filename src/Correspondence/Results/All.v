Require Export
  Bourbaki.Correspondence.Relation.SymmetricGraphEssence
  Bourbaki.Correspondence.Results.Diagonal
  Bourbaki.Correspondence.Results.Product
  Bourbaki.Correspondence.Results.ReverseApplication
  Bourbaki.Correspondence.Results.Surjectivity
  Bourbaki.Set.Results.Meta.Emptiness.

Module RetractionEssence.
  Section RetractionEssence.
    Context `{Set_.Theory}.

    Theorem commutativity {Y X} (g : Y → X) (f : X → Y) :
      ⊢ is_retraction g f ⇔ is_section f g.
    Proof.
      Reflexivity.
    Qed.
  End RetractionEssence.
End RetractionEssence.

Module SectionEssence.
  Section SectionEssence.
    Context `{Set_.Theory}.

    Theorem commutativity {Y X} (g : Y → X) (f : X → Y) :
      ⊢ is_section g f ⇔ is_retraction f g.
    Proof.
      Reflexivity.
    Qed.
  End SectionEssence.
End SectionEssence.

Module Bijectivity.
  Section Bijectivity.
    Context `{Set_.Theory}.

    (* Corr_E_II_3__2 *)
    Theorem from_retraction_section {Y X} (g : Y → X) (f : X → Y) :
      ⊢ is_retraction g f ⇒ is_section g f ⇒
        is_bijective f ∧ is_bijective g ∧ g = f⁻¹.
    Proof.
      Intros H₁ H₂ [[|] | [[|] |]].
      { Apply (Injectivity.from_retraction g).
        Assumption. }
      { Apply (Surjectivity.from_section g).
        Assumption. }
      { Apply (Injectivity.from_retraction f).
        Apply RetractionEssence.commutativity.
        Assumption. }
      { Apply (Surjectivity.from_section f).
        Apply SectionEssence.commutativity.
        Assumption. }
      { Apply Application.equality_when_same_domainₑ.
        Intros y H₃.
        admit. }
    Qed.
  End Bijectivity.
End Bijectivity.

Module Diagonal.
  Section Diagonal.
    Context `{Set_.Theory}.

    Theorem symmetry :
      ⊢ ∀ X, is_symmetric_graph (Δ X).
    Proof.
      Rewrite Graph.equalityₑ.
      Intros X x y.
      do 2 (Rewrite CoupleMembershipEquivalenceProof.proof).
      Rewrite (fun x X => Conjunction.commutativity (x ∈ X)).
      Rewrite Equality.commutativity at 1.
      Apply (Equality.as_conjunct_leftₑ _ _ (fun y => y ∈ X)).
    Qed.
  End Diagonal.
End Diagonal.

Module Graph.
  Section Graph.
    Context `{Set_.Theory}.

    Theorem subset_of_product_essence (G : Graph) :
      ⊢ G ⊂ pr₁⟨G⟩ × pr₂⟨G⟩.
    Proof.
      Apply Graph.inclusionₑ.
      Rewrite CoupleMembershipEquivalenceProof.proof.
      Rewrite MembershipEquivalenceProof.proof.
      Intros x y H₁ [[] | []];
        Assumption.
    Qed.

    Theorem emptiness (G : Graph) :
      ⊢ is_empty pr₁⟨G⟩ ∨ is_empty pr₂⟨G⟩ ⇒ is_empty G.
    Proof.
      Rewrite Graph.subset_of_product_essence.
      Apply Product.emptinessₑ.
    Qed.
  End Graph.
End Graph.

Module Product.
  Section Product.
    Context `{Set_.Theory}.

    Theorem reverseₑ :
      ⊢ ∀ X Y, (X × Y)⁻¹ = Y × X.
    Proof.
      Rewrite Graph.equalityₑ.
      Intros X Y y x.
      do 2 (Rewrite CoupleMembershipEquivalenceProof.proof).
      Apply Conjunction.commutativity.
    Qed.
  End Product.
End Product.

Module ReverseApplication.
  Section ReverseApplication.
    Context `{Set_.Theory}.

    Theorem composite_leftₑ {X Y} (f : X → Y) `(!IsBijective f) :
      ⊢ f⁻¹ ∘ f = Id X.
    Proof.
      Apply Application.equality_when_same_domainₑ.
      Intros x H₁.
      Rewrite ValueEqualityProof.proof.
      Symmetry.
      assert (H₄ : ⊢ f x ∈ Y). {
        Apply (Correspondence.second_projection_subset_essence (G := f)).
        Apply Value.element_essence.
      }
      Apply Value.as_equalₑ.
      Apply CoupleMembershipEquivalenceProof.proof; Change (⊢ _ ∈ _).
      Apply Value.value_essence.
    Qed.

    Theorem composite_rightₑ {X Y} (f : X → Y) `(!IsBijective f) :
      ⊢ f ∘ f⁻¹ = Id Y.
    Proof.
      Apply Application.equality_when_same_domainₑ.
      Intros y H₁.
      Rewrite ValueEqualityProof.proof.
      Apply ReverseApplication.value_passed_to_reversed_application.
      Assumption.
    Qed.
  End ReverseApplication.
End ReverseApplication.

Module Other.
  Section Other.
    Context `{Set_.Theory}.

    Lemma Rem_E_II_3__1 :
      ⊢ ¬has_graph (fun x y => x = y).
    Proof.
      Intros [G [contra₁ contra₂]].
      Apply Other.Rem_E_II_1__2.
      Intros [x].
      Rewrite (MembershipEquivalenceProof.proof pr₁⟨G⟩).
      Rewrite <- contra₂.
      Apply Equality.reflexivity.
    Qed.

    Lemma Pr_E_II_3__2 G :
      ⊢ ∀ X Y, X ⊂ Y ⇒ G⟨X⟩ ⊂ G⟨Y⟩.
    Proof.
      Intros X Y H₁.
      Rewrite H₁.
    Qed.

    Lemma Exa_E_II_3_7__6 {X Y} (f : X → Y) :
      ⊢ is_surjective (x ∈ X ↦ f x).
    Proof.
      unfold is_surjective.
      Rewrite Image.of_starting_set.
      Apply TermFunction.second_projectionₑ.
    Qed.
  End Other.

  Section Exa_E_II_3_7__5.
    Context `{Set_.Theory}.

    Instance :
      forall y X, set_by_replacement (fun x => ❨x, y❩) X ⊢⊂ X × {y,}.
    Proof.
      Change (forall y X, ⊢ ∀ z, _).
      Rewrite MembershipEquivalenceProof.proof at 1.
      Intros y X z [x H₁].
      Rewrite H₁.
      Apply CoupleMembershipEquivalenceProof.proof.
      Intros [|].
      { Assumption. }
      { Apply MembershipEquivalenceProof.proof.
        Reflexivity. }
    Qed.

    Lemma Exa_E_II_3_7__5_i :
      ⊢ ∀ X y, is_injective (x ∈ X ↦ ❨x, y❩ ∈ X × {y,}).
    Proof.
      Intros X y.
      Apply Injectivity.alternative_definition.
      Intros x₁ H₁ x₂ H₂.
      Rewrite ValueEqualityProof.proof.
      Rewrite Couple.equalityₑ.
      Apply Conjunction.elimination_left.
    Qed.

    Lemma Exa_E_II_3_7__5_ii :
      ⊢ ∀ X y, is_surjective (x ∈ X ↦ ❨x, y❩ ∈ X × {y,}).
    Proof.
      Intros X y.
      unfold is_surjective.
      Rewrite Image.of_starting_set.
      Rewrite TermFunction.second_projectionₑ.
      Apply Set_.equalityₑ.
      Intros z.
      do 2 (Rewrite MembershipEquivalenceProof.proof);
        Change (⊢ _ ⇔ ∃ x y', _).
      Rewrite Conjunction.associativity.
      Rewrite <- (fun _ => Conjunction.commutativity (_ = _)).
      Rewrite Existence.of_equalₑ.
    Qed.

    Lemma Exa_E_II_3_7__5_iii :
      ⊢ ∀ X y, is_bijective (x ∈ X ↦ ❨x, y❩ ∈ X × {y,}).
    Proof.
      Intros X y [|].
      { Apply Exa_E_II_3_7__5.Exa_E_II_3_7__5_i. }
      { Apply Exa_E_II_3_7__5.Exa_E_II_3_7__5_ii. }
    Qed.
  End Exa_E_II_3_7__5.
End Other.