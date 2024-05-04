Require Export
  Bourbaki.Formal.Syntax
  Bourbaki.Truth.Notation.

Module Truth.
  Class Syntax `{Formal.Syntax} := {
    truth : Relation
  }.
End Truth.

Notation "⊤" := Truth.truth : bourbaki_scope.