Require Export
  Bourbaki.Equality.Notation
  Bourbaki.Formal.Syntax.

Module Equality.
  Class Syntax `{Formal.Syntax} := {
    (* relation d'égalité *)
    equality : Term -> Term -> Relation
  }.
End Equality.

Infix "=" := Equality.equality : bourbaki_scope.