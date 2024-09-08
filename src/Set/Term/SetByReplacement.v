Require Export
  Bourbaki.Set.Term.CollectivizingSet.

(* l'ensemble des objets de la forme 𝐓 pour x ∈ X *)
Definition set_by_replacement `{Set_.Syntax} 𝐓 X :=
{y | ∃ x, y = 𝐓 x ∧ x ∈ X}.