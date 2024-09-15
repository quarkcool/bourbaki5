Require Export
  Bourbaki.Correspondence.Term.Graph
  Bourbaki.Set.Results.All.

Module Graph.
  Section Graph.
    Context `{Set_.Theory}.

    Fact inclusion_rewrite_lemma {G₁ G₂} (H₁ : ⊢ G₁ ⊂ G₂) :
      RewriteLemma
        H₁
        (forall `(!IsGraph G₁) `(!IsGraph G₂), (G₁ : Graph) ⊢⊂ (G₂ : Graph)).
    Proof.
      split.
      Intros H₂ H₃.
      Assumption.
    Defined.

    Theorem typical_universalityₑ (G : Graph) 𝐑 :
      ⊢ (∀ z ⟨∈ G⟩, 𝐑 z) ⇔ ∀ x y, ❨x, y❩ ∈ G ⇒ 𝐑 ❨x, y❩.
    Proof.
      Rewrite <- TypicalUniversality.over_couplesₑ.
      Rewrite (_ : ∀ z ⟨is_couple⟩, _ ⊢⇔ ∀ z ⟨is_couple⟩, z ∈ G ⇒ 𝐑 z).
      { Apply TypicalUniversality.conditional_rewriting.
        Intros z H₂.
        Rewrite <- CoupleEssence.alternative_definition;
          Assumption. }
      { Change (⊢ _ ⇔ ∀ z, _).
        Rewrite <- Conjunction.as_conditionₑ.
        Rewrite (fun _ => Conjunction.operand_removal_left _ (is_couple _)).
        Apply G.(graph_essence). }
    Qed.

    Theorem inclusionₑ (G : Graph) :
      ⊢ ∀ X, G ⊂ X ⇔ ∀ x y, ❨x, y❩ ∈ G ⇒ ❨x, y❩ ∈ X.
    Proof.
      Intros X.
      Apply Graph.typical_universalityₑ.
    Qed.

    Theorem typical_existenceₑ (G : Graph) 𝐑 :
      ⊢ (∃ z ⟨∈ G⟩, 𝐑 z) ⇔ ∃ x y, ❨x, y❩ ∈ G ∧ 𝐑 ❨x, y❩.
    Proof.
      Rewrite <- TypicalExistence.of_coupleₑ.
      Rewrite (_ : ∃ z ⟨is_couple⟩, _ ⊢⇔ ∃ z ⟨is_couple⟩, z ∈ G ∧ 𝐑 z).
      { Apply TypicalExistence.conditional_rewriting.
        Intros z H₂.
        Rewrite <- CoupleEssence.alternative_definition;
          Assumption. }
      { Change (⊢ _ ⇔ ∃ z, _).
        Rewrite Conjunction.associativity.
        Rewrite (fun _ => Conjunction.operand_removal_left _ (is_couple _)).
        Apply G.(graph_essence). }
    Qed.
  End Graph.

  Hint Extern 1 (RewriteLemma _ _) =>
    notypeclasses refine (inclusion_rewrite_lemma _) :
  rewrite_lemma_instances.
End Graph.
Export (hints) Graph.