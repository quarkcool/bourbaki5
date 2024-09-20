Require Export
  Bourbaki.Correspondence.Term.Value.

(* f et g coïncident dans [l'ensemble] Z *)
Definition coincidence
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}
  {X₁ Y₁ X₂ Y₂} (f : X₁ → Y₁) (g : X₂ → Y₂) Z :=
(Z ⊂ X₁ ∧ Z ⊂ X₂) ∧ ∀ x ⟨∈ Z⟩, f x = g x.