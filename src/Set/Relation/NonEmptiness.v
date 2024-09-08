Require Export
  Bourbaki.Quantification.Relation.Existence
  Bourbaki.Set.Syntax.

(* X est un ensemble non-vide *)
Definition is_non_empty `{Set_.Syntax} X := ∃ x, x ∈ X.