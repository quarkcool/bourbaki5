Require Export
  Bourbaki.Correspondence.Correspondence.TermFunction
  Bourbaki.Correspondence.Relation.Surjectivity
  Bourbaki.Correspondence.Results.Image.

Section CanonicalSection.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall {X Y} (f : X → Y) `(!IsSurjective f),
      set_by_replacement (fun y => τ x, x ∈ X ∧ f x = y) Y ⊢⊂ X.
  Proof.
    Change (forall X Y f H₁, ⊢ ∀ x', _).
    Rewrite MembershipEquivalenceProof.proof.
    Intros X Y f H₁ x' [y H₂].
    Rewrite H₂.
    Apply Conjunction.elimination_left.
    Rewrite <- (Existence.definition (fun x => x ∈ X ∧ _)).
    Rewrite Equality.commutativity.
    Apply (MembershipEquivalenceProof.proof f⟨X⟩).
    Rewrite H₁.
    Assumption.
  Qed.

  Definition canonical_section {X Y} (f : X → Y) `{!IsSurjective f} :=
  y ∈ Y ↦ (τ x, x ∈ X ∧ f x = y) ∈ X.
End CanonicalSection.