Require Export
  Bourbaki.Formal.Syntax
  Bourbaki.Logic.Truth.Notation.

Module Logic.
  Module Truth.
    Class Syntax `{Formal.Syntax} := {
      truth : Relation
    }.
  End Truth.
End Logic.
Export Logic.Truth (truth).

Notation "⊤" := truth : bourbaki_scope.

Notation "⊥" := (¬⊤) : bourbaki_scope.