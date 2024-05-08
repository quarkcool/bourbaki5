Require Export
  Bourbaki.Equality.Relation.AtMostOneExistence
  Bourbaki.Formal.Meta.StrongerTheoryEssence.

(* relation univoque dans 𝒯₁ *)
Class SingleValuedRelation `{Equality.Syntax} 𝒯₁ 𝐑 :=
single_valued_essence :
  forall {𝒯₂} `(𝒯₂ ⟫ 𝒯₁), 𝒯₂ ⊢ at_most_one_existence 𝐑.