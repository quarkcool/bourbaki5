Require Export
  Bourbaki.Correspondence.Correspondence.IdenticalApplication
  Bourbaki.Correspondence.Term.GraphComposite.

(*
  Def_E_II_3__11_i /
  r est une rétraction associée à f /
  r est une inverse à gauche associée à f
*)
Definition is_retraction `{Set_.Theory} {Y X} (r : Y → X) (f : X → Y) :=
r ∘ f = Id X.