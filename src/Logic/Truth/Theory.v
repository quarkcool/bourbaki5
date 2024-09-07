Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Logic.Truth.Syntax.

Module Logic.
  Module Truth.
    Class Theory `{Logic.Truth.Syntax, !Formal.Theory} := {
      truth_truth : ⊢ ⊤
    }.
  End Truth.
End Logic.