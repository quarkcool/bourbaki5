Require Export
  Bourbaki.Set.Relation.Emptiness.

(* l'ensemble vide *)
Definition empty_set `{Set_.Syntax} := τ x, is_empty x.

Notation "∅" := empty_set : bourbaki_scope.