Require Export
  Bourbaki.Equality.Syntax
  Bourbaki.Formal.Relation.Implication
  Bourbaki.Quantification.Relation.Universality.

(* il existe au plus un x tel que 𝐑 *)
Definition at_most_one_existence `{Equality.Syntax} 𝐑 :=
∀ x₁ x₂, 𝐑 x₁ ⇒ 𝐑 x₂ ⇒ x₁ = x₂.