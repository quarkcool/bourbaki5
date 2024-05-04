Require Export
  Bourbaki.Falsity.Syntax
  Bourbaki.Formal.Theory.

Module Falsity.
  Class Theory `{Falsity.Syntax, !Formal.Theory} := {
    falsity_impossibility : ⊢ ¬⊥
  }.
End Falsity.