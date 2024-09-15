Require Export
  Bourbaki.Correspondence.Results.Meta.Graph
  Bourbaki.Correspondence.Results.Meta.Product.

Section Product.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall X Y, IsGraph (X × Y).
  Proof.
    Change (forall X Y, ⊢ ∀ z, _).
    Rewrite MembershipEquivalenceProof.proof.
    Intros X Y z [x [y H₁]].
    Rewrite H₁.
    Apply Couple.couple_essence.
  Qed.

  (* Pr_E_II_2__2 *)
  Theorem inclusionₑ :
    ⊢ ∀ X₁ Y₁ ⟨is_non_empty⟩, ∀ X₂ Y₂, X₁ × Y₁ ⊂ X₂ × Y₂ ⇔ X₁ ⊂ X₂ ∧ Y₁ ⊂ Y₂.
  Proof.
    Intros X₁ H₁ Y₁ H₂ X₂ Y₂.
    Rewrite (Graph.inclusionₑ (X₁ × Y₁)).
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite Conjunction.as_consequenceₑ.
    do 2 (Rewrite Universality.split);
      Change (⊢ (∀ x y, _) ∧ (∀ x y, _) ⇔ _).
    Rewrite Universality.switch at 2.
    Rewrite (fun _ => Conjunction.commutativity (_ ∈ X₁)) at 2.
    Rewrite Conjunction.as_conditionₑ.
    Rewrite Universality.condition_extraction;
      Change (⊢ (∀ x, _ ⇒ ∀ y, _) ∧ _ ⇔ _).
    Rewrite Universality.consequence_extraction;
      Change (⊢ (∀ x, _ ⇒ (∃ y, _) ⇒ _) ∧ _ ⇔ _).
    Rewrite (
      fun 𝐀 x => Implication.with_true_condition 𝐀 (is_non_empty x)
    ).
    all:
      Assumption.
  Qed.
End Product.