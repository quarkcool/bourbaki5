Require Export
  Bourbaki.Equality.Relation.UniqueExistence
  Bourbaki.Formal.Meta.StrongerTheoryEssence.

(* relation fonctionnelle dans 𝒯₁ *)
Class FunctionalRelation `{Equality.Syntax} 𝒯₁ 𝐑 :=
functional_essence : forall {𝒯₂} `(𝒯₂ ⟫ 𝒯₁), 𝒯₂ ⊢ unique_existence 𝐑.