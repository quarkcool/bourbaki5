Require Export
  Bourbaki.Correspondence.Correspondence.Restriction
  Bourbaki.Correspondence.Relation.ExtensionEssence
  Bourbaki.Correspondence.Results.TermFunction.

Section Restriction.
  Context `{Set_.Theory}.

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
    { Apply Application.inclusionₑ.
      Intros [| [[|] | x H₁]].
      1,3: Assumption.
      { Reflexivity. }
      { Apply ValueEqualityProof.proof. } }
    { Reflexivity. }
  Qed.
End Restriction.