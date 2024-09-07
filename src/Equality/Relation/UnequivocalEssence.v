Require Export
  Bourbaki.Equality.Relation.AtMostOneExistence
  Bourbaki.Formal.Theory.

#[local] Set Typeclasses Unique Instances.
(* 𝐑 est univoque en x *)
Class IsUnequivocal `{Formal.Theory, !Equality.Syntax} 𝐑 :=
unequivocal_essence : ⊢ at_most_one_existence 𝐑.

Hint Extern 0 (⊢ at_most_one_existence _) =>
  notypeclasses refine unequivocal_essence :
typeclass_instances.