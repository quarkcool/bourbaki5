Require Export
  Bourbaki.Set.Term.Pair.

(* l'ensemble dont le seul élément est x *)
Definition singleton `{Set_.Syntax} x := {x, x}.

Notation "{ x , }" := (singleton x) : bourbaki_scope.