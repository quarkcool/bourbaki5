Require Export
  Bourbaki.Set.Term.Couple.

(* z est un couple *)
Definition is_couple `{Set_.Syntax} z := ∃ x y, z = ❨x, y❩.