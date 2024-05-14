Require Export
  Bourbaki.Formal.Model.Meta.StrongerTheoryEssence
  Bourbaki.Formal.Model.Meta.TheoryWithoutSomeAxioms.

(* l'axiome [𝐀] de 𝒯 est indépendant des autres *)
Definition AxiomIndependence `(𝒯 : Theory) 𝐀 :=
𝐀 ∈ 𝒯.(ExplicitAxioms) -> 𝒯 \ {𝐀,} ⊃ 𝒯 -> False.