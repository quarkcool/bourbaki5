Require Export
  Bourbaki.Logic.Results.Conjunction
  Bourbaki.Set.Results.Meta.Inclusion.

Import Proof.TheoryHidingNotation.

Section Examples.
  Context `(QuantifiedTheory, !Equality.Syntax, !Set_.Syntax).

  Example PROP2 x y z :
    𝒯 ⊢ x ⊂ y ∧ y ⊂ z ⇒ x ⊂ z.
  Proof.
    Rewrite Conjunction.as_conditionₑ.
    Apply Inclusion.transitivity.
  Defined.
End Examples.