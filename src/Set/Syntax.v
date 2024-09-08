Require Export
  Bourbaki.Equality.Syntax
  Bourbaki.Set.Notation.

Module Set_.
  Class Syntax `{Equality.Syntax} := {
    (* relation d'appartenance *)
    membership : Term -> Term -> Relation
  }.
End Set_.
Export Set_ (membership).

Infix "∈" := membership : bourbaki_scope.

Notation "∈ X" := (fun x => x ∈ X) : bourbaki_scope.