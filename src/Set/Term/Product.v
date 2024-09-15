Require Export
  Bourbaki.Set.Term.Couple.

(* Def_E_II_2__1 / produit de X et Y *)
Definition product `{Set_.Syntax} X Y :=
{z | ∃ x y, z = ❨x, y❩ ∧ x ∈ X ∧ y ∈ Y}.

Infix "×" := product : bourbaki_scope.