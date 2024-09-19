Require Export
  Bourbaki.Set.Term.Couple
  Bourbaki.Set.Term.SetByReplacement.

(* Def_E_II_3__8 / diagonale de X × X *)
Definition Δ `{Set_.Syntax} X := set_by_replacement (fun x => ❨x, x❩) X.