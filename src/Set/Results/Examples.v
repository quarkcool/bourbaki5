Require Export
  Bourbaki.Logic.Results.Conjunction
  Bourbaki.Quantification.Results.Meta.Rewriting
  Bourbaki.Set.Results.Meta.Inclusion
  Bourbaki.Set.Results.Theory.

Import Proof.TheoryHidingNotation.

Section Examples.
  Context `(SetTheory).

  Example PROP2 x y z :
    𝒯 ⊢ x ⊂ y ∧ y ⊂ z ⇒ x ⊂ z.
  Proof.
    Rewrite Conjunction.as_conditionₑ.
    Apply Inclusion.transitivity.
  Defined.

  Example A1 :
    𝒯 ⊢ ∀ x y, x ⊂ y ∧ y ⊂ x ⇒ x = y.
  Proof.
    Rewrite Conjunction.as_conditionₑ.
    Apply Set_.extensionality.
  Defined.
End Examples.