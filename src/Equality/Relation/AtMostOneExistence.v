Require Export
  Bourbaki.Equality.Syntax
  Bourbaki.Quantification.Relation.TypicalUniversality.

(* il existe au plus un x tel que 𝐑 *)
Definition at_most_one_existence `{Equality.Syntax} 𝐑 := ∀ x y ⟨ 𝐑 ⟩, x = y.
Hint Transparent at_most_one_existence : introduction_pattern_instances.