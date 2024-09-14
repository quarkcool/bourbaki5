Require Export
  Bourbaki.Set.Term.Singleton.

(* couple formé de x et de y *)
Definition couple `{Set_.Syntax} x y := {{x,}, {x, y}}.

Notation "❨ x , y ❩" := (couple x y) : bourbaki_scope.