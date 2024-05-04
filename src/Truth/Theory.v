Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Truth.Syntax.

Module Truth.
  Class Theory `{Truth.Syntax, !Formal.Theory} := {
    truth_truth : ⊢ ⊤
  }.
End Truth.