Require Export
  Bourbaki.Logic.Theory
  Bourbaki.Quantification.Relation.Existence.

Module Quantification.
  Class Theory `{Logic.Theory} := {
    (* S5 *)
    existence_introduction : forall 𝐑 x, ⊢ 𝐑 x ⇒ ∃ x, 𝐑 x
  }.
End Quantification.