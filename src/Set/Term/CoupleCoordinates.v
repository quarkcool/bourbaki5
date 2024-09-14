Require Export
  Bourbaki.Set.Term.Couple.

(* première coordonnée de z / première projection de z *)
Definition pr₁ `{Set_.Syntax} z := τ x, ∃ y, z = ❨x, y❩.

(* seconde coordonnée de z / seconde projection de z *)
Definition pr₂ `{Set_.Syntax} z := τ y, ∃ x, z = ❨x, y❩.