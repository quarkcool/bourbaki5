Require Export
  Bourbaki.Equality.Syntax
  Bourbaki.Set.Notation.

Module Set_.
  Class Syntax `{Equality.Syntax} := {
    (* relation d'appartenance *)
    membership : Term -> Term -> Relation
  }.
End Set_.

Infix "∈" := Set_.membership : bourbaki_scope.

Notation "∈ x" := (fun y => y ∈ x) : bourbaki_scope.