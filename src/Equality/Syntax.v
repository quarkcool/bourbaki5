Require Export
  Bourbaki.Equality.Notation
  Bourbaki.Formal.Syntax
  Bourbaki.Meta.Util.

Module Equality.
  Class Syntax `{Formal.Syntax} := {
    (* relation d'égalité *)
    equality : Term -> Term -> Relation
  }.
End Equality.
Export Equality (equality).

Infix "=" := equality : bourbaki_scope.

Notation "= y" := (fun x => x = y) : bourbaki_scope.

#[export]
Instance :
  forall `{Equality.Syntax}, Inhabited Term :=
fun _ _ => τ x, x = x.