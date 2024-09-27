Require Export
  Bourbaki.Correspondence.Relation.Injectivity
  Bourbaki.Correspondence.Relation.RetractionEssence
  Bourbaki.Correspondence.Results.FunctionComposite.

Section Injectivity.
  Context `{Set_.Theory}.

  Theorem alternative_definition {X Y} (f : X → Y) :
    ⊢ is_injective f ⇔ ∀ x₁ x₂ ⟨∈ X⟩, f x₁ = f x₂ ⇒ x₁ = x₂.
  Proof.
    Rewrite (fun _ _ => Implication.contrapositiveₑ (_ = _)).
  Qed.

  (* Pr_E_II_3__8_i *)
  Theorem from_retraction {Y X} (r : Y → X) (f : X → Y) :
    ⊢ is_retraction r f ⇒ is_injective f.
  Proof.
    Rewrite Application.equality_when_same_domainₑ.
    Rewrite Injectivity.alternative_definition.
    Intros H₁ x₁ H₂ x₂ H₃ H₄.
    Rewrite <- (ValueEqualityProof.proof _ _ (Id X) (fun x => x)).
    Rewrite <- H₁.
    { Rewrite ValueEqualityProof.proof.
      Rewrite H₄. }
    all: Assumption.
  Qed.
End Injectivity.