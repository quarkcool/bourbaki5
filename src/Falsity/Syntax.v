Require Export
  Bourbaki.Falsity.Notation
  Bourbaki.Formal.Syntax.

Module Falsity.
  Class Syntax `{Formal.Syntax} := {
    falsity : Relation
  }.
End Falsity.

Arguments Falsity.falsity : simpl never.

Notation "⊥" := Falsity.falsity : bourbaki_scope.