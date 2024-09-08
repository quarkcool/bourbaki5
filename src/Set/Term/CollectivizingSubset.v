Require Export
  Bourbaki.Set.Term.CollectivizingSet.

(* l'ensemble des x ∈ X tels que 𝐑 *)
Definition collectivizing_subset `{Set_.Syntax} 𝐑 X := {x | 𝐑 x ∧ x ∈ X}.

Notation "{ x ∈ X | 𝐑 }" :=
  (collectivizing_subset (fun x => 𝐑) X) :
bourbaki_scope.