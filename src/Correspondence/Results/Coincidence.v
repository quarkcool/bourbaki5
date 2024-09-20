Require Export
  Bourbaki.Correspondence.Relation.Coincidence
  Bourbaki.Equality.Results.Meta.Equality
  Bourbaki.Logic.Results.Conjunction
  Bourbaki.Quantification.Results.Meta.TypicalUniversality
  Coq.Classes.Equivalence.

Section Coincidence.
  Context `{Equality.Theory, !Set_.Syntax}.

  Theorem commutativity {X₁ Y₁ X₂ Y₂} (f : X₁ → Y₁) (g : X₂ → Y₂) :
    ⊢ ∀ X, coincidence f g X ⇔ coincidence g f X.
  Proof.
    Intros X.
    unfold coincidence.
    Rewrite (Conjunction.commutativity (_ ⊂ _)).
    Rewrite (fun _ => ⇑Equality.commutativity (f _)).
  Qed.
End Coincidence.