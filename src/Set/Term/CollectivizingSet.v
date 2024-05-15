Require Export
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Set.Syntax.

(* l'ensemble des x tels que 𝐑 *)
Definition collectivizing_set `{Set_.Syntax} 𝐑 := τ y, ∀ x, x ∈ y ⇔ 𝐑 x.

Notation "{ x | 𝐑 }" := (collectivizing_set (fun x => 𝐑)) : bourbaki_scope.