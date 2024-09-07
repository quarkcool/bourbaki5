Require Export
  Bourbaki.Equality.Relation.UniqueExistence
  Bourbaki.Formal.Theory.

#[local] Set Typeclasses Unique Instances.
(* 𝐑 est fonctionnelle en x *)
Class IsFunctional `{Formal.Theory, !Equality.Syntax} 𝐑 :=
functional_essence : ⊢ unique_existence 𝐑.