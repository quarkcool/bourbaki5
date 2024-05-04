Require Export
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Logic.Results.Meta.Conjunction.

Import Proof.TheoryHidingNotation.

Section Negation.
  Context `(LogicalTheory).

  (* C24_a *)
  Theorem double_removal 𝐀 :
    𝒯 ⊢ ¬¬𝐀 ⇔ 𝐀.
  Proof.
    Intros [|].
    { Apply Negation.doubling. }
    { Apply Negation.double_removal. }
  Defined.
End Negation.