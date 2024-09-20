Require Export
  Bourbaki.Correspondence.Term.Value.

#[local] Set Typeclasses Unique Instances.
Class ValueEqualityProof
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} {X Y} (f : X → Y) 𝐓 :=
proof : forall x : Element X, ⊢ f x = 𝐓 x.

Arguments proof {_ _ _ _}.