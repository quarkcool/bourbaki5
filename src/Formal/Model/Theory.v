Require Export
  Bourbaki.Formal.Syntax
  Bourbaki.Util.Set.

Declare Scope bourbaki_theory_scope.

Class Theory `{Formal.Syntax} := {
  (* axiomes explicites *)
  #[canonical=no] ExplicitAxioms : Set_ Relation;

  (* schémas *)
  Schemas : Set_ Relation
}.
Bind Scope bourbaki_theory_scope with Theory.

Arguments ExplicitAxioms {_}.
Arguments Schemas {_}.