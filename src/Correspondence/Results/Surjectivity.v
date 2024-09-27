Require Export
  Bourbaki.Correspondence.Relation.SectionEssence
  Bourbaki.Correspondence.Relation.Surjectivity
  Bourbaki.Correspondence.Results.FunctionComposite.

Section Surjectivity.
  Context `{Set_.Theory}.

  (* Pr_E_II_3__8_ii *)
  Theorem from_section {Y X} (s : Y → X) (f : X → Y) :
    ⊢ is_section s f ⇒ is_surjective f.
  Proof.
    Rewrite Application.equality_when_same_domainₑ.
    Rewrite (⇑Set_.equalityₑ₂ f⟨X⟩).
    Intros H₁ [| y H₂].
    { Rewrite Image.of_starting_set.
      Apply Correspondence.second_projection_subset_essence. }
    { Apply MembershipEquivalenceProof.proof.
      Intros [].
      Apply Conjunction.operand_removal_right.
      { Intros H₃.
        Rewrite <- (ValueEqualityProof.proof _ _ (Id Y) (fun x => x)).
        Rewrite <- H₁.
        { Rewrite ValueEqualityProof.proof at 1. }
        { Assumption. } }
      { Apply (Correspondence.second_projection_subset_essence (G := s)).
        Apply Value.element_essence. } }
  Qed.
End Surjectivity.