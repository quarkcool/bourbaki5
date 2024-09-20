Require Export
  Bourbaki.Correspondence.Relation.Coincidence.

(* g est un prolongement de f [à X₂] / g prolonge f [à X₂] *)
Definition is_extension
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}
  {X₁ Y₁ X₂ Y₂} (f : X₁ → Y₁) (g : X₂ → Y₂) :=
f ⊂ g ∧ Y₁ ⊂ Y₂.