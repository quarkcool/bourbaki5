Require Export
  Bourbaki.Set.Term.CollectivizingSet.

(* DEF2 / l'ensemble dont les seuls éléments sont x et y *)
Definition pair `{Set_.Syntax} x y := {z | z = x ∨ z = y}.

Notation "{ x , y }" := (pair x y) : bourbaki_scope.