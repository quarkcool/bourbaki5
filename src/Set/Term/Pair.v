Require Export
  Bourbaki.Set.Term.CollectivizingSet.

(* Def_E_II_1__2 *)
Definition pair `{Set_.Syntax} x y := {z | z = x ∨ z = y}.

Notation "{ x , y }" := (pair x y) : bourbaki_scope.