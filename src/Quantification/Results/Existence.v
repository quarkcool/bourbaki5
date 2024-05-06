Require Export
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Logic.Results.Meta.Conjunction
  Bourbaki.Quantification.Results.Meta.Existence.

Import Proof.TheoryHidingNotation.

Section Existence.
  Context `(QuantifiedTheory).

  (* C34_b *)
  Theorem switch 𝐑 :
    𝒯 ⊢ (∃ x y, 𝐑 x y) ⇔ ∃ y x, 𝐑 x y.
  Proof.
    Intros [[x [y H₁]] | [y [x H₁]]];
      Assumption.
  Defined.
End Existence.