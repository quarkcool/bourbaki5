Require Export
  Bourbaki.Correspondence.Correspondence.Restriction
  Bourbaki.Correspondence.Relation.ExtensionEssence
  Bourbaki.Correspondence.ValueEqualityProof.

Section Restriction.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall {X₁ Y X₂} (f : X₁ → Y) `(!X₂ ⊢⊂ X₁),
      ValueEqualityProof (f ∥ X₂) (value f).
  Proof.
    Intros X₁ Y X₂ f H₁ x.
    Apply Application.inclusionₑ.
    { Apply RelationSubgraph.subset_essence. }
    { Apply Element.membership. }
  Qed.

  Theorem equalityₑ
    {X₁ Y₁ X₂ Y₂ X₃} (f : X₁ → Y₁) (g : X₂ → Y₂) `(!X₃ ⊢⊂ X₁) `(!X₃ ⊢⊂ X₂) :
      ⊢ f ∥ X₃ = g ∥ X₃ ⇔ coincidence f g X₃.
  Proof.
    Rewrite Application.equality_when_same_domainₑ.
    Rewrite (Conjunction.operand_removal_left _ (_ ∧ _)).
    { Apply TypicalUniversality.conditional_rewriting.
      Intros x H₁.
      Rewrite ValueEqualityProof.proof. }
    { Intros _ [|];
        Assumption. }
  Qed.

  Theorem extended_essence {X₁ Y X₂} (f : X₁ → Y) `(!X₂ ⊢⊂ X₁) :
    ⊢ is_extension (f ∥ X₂) f.
  Proof.
    Intros [|].
    { Apply RelationSubgraph.subset_essence. }
    { Reflexivity. }
  Qed.
End Restriction.