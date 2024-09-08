Require Export
  Bourbaki.Set.Results.Emptiness
  Bourbaki.Set.Term.EmptySet.

Section EmptySet.
  Context `{Set_.Theory}.

  Theorem as_equalₑ :
    ⊢ ∀ x, x = ∅ ⇔ is_empty x.
  Proof.
    Intros x.
    Rewrite <- FunctionalEssence.common_term.
  Qed.

  Theorem emptiness :
    ⊢ is_empty ∅.
  Proof.
    Rewrite <- Existence.definition.
    Apply Emptiness.functional_essence.
  Qed.

  Theorem typical_universality 𝐑 :
    ⊢ ∀ x ⟨∈ ∅⟩, 𝐑 x.
  Proof.
    Intros x H₁.
    Exfalso.
    Apply EmptySet.emptiness;
    Assumption.
  Qed.

  Theorem subset_essence :
    ⊢ ∀ x, ∅ ⊂ x.
  Proof.
    Intros x.
    Apply EmptySet.typical_universality.
  Qed.

  #[export]
  Instance :
    forall x, ∅ ⊢⊂ x.
  Proof.
    Intros x.
    Apply EmptySet.subset_essence.
  Qed.

  Theorem as_supersetₑ :
    ⊢ ∀ x, x ⊂ ∅ ⇔ x = ∅.
  Proof.
    Intros x.
    Rewrite Set_.equalityₑ₂.
    Rewrite (Conjunction.operand_removal_right (_ ⊂ _)).
    Apply EmptySet.subset_essence.
  Qed.
End EmptySet.