Require Export
  Bourbaki.Correspondence.Correspondence.IdenticalApplication
  Bourbaki.Correspondence.Term.GraphComposite.

(*
  Def_E_II_3__11_ii /
  s est une section associée à f /
  s est une inverse à droite associée à f
*)
Definition is_section `{Set_.Theory} {Y X} (s : Y → X) (f : X → Y) :=
f ∘ s = Id Y.