Require Export
  Bourbaki.Equality.Relation.AtMostOneExistence
  Bourbaki.Logic.Relation.Conjunction.

(* il existe un x et un seul tel que 𝐑 *)
Definition unique_existence `{Equality.Syntax} 𝐑 :=
(∃ x, 𝐑 x) ∧ at_most_one_existence 𝐑.