Require Export
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Set.Relation.NonMembership.

(* l'ensemble X est vide *)
Definition is_empty `{Set_.Syntax} X := ∀ x, x ∉ X.