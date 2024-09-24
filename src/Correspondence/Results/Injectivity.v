Require Export
  Bourbaki.Correspondence.Relation.Injectivity
  Bourbaki.Equality.Results.Meta.Truth
  Bourbaki.Logic.Results.Implication
  Bourbaki.Quantification.Results.Meta.TypicalUniversality
  Coq.Classes.Equivalence.

Section Injectivity.
  Context `{Quantification.Theory, !Equality.Syntax, !Set_.Syntax}.

  Theorem alternative_definition {X Y} (f : X → Y) :
    ⊢ is_injective f ⇔ ∀ x₁ x₂ ⟨∈ X⟩, f x₁ = f x₂ ⇒ x₁ = x₂.
  Proof.
    Rewrite (fun _ _ => Implication.contrapositiveₑ (_ = _)).
  Qed.
End Injectivity.