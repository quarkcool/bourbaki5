Require Export
  Bourbaki.Logic.Results.Negation
  Bourbaki.Quantification.Relation.Universality.

Import Proof.TheoryHidingNotation.

Section Universality.
  Context `(LogicalTheory).

  (* C28 *)
  Theorem negationₑ 𝐑 :
    𝒯 ⊢ ¬(∀ x, 𝐑 x) ⇔ ∃ x, ¬𝐑 x.
  Proof.
    Apply Negation.double_removal.
  Defined.
End Universality.