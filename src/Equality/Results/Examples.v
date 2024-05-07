Require Export
  Bourbaki.Equality.Results.Meta.Rewriting
  Bourbaki.Logic.Results.Conjunction.

Import Proof.TheoryHidingNotation.

Section Examples.
  Context `(EqualitarianTheory).

  Example TH3 x y z :
    𝒯 ⊢ x = y ∧ y = z ⇒ x = z.
  Proof.
    Rewrite Conjunction.as_conditionₑ.
    Apply Equality.transitivity.
  Defined.

  Example C44 T U V :
    𝒯 ⊢ T = U ⇒ V T = V U.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.
End Examples.