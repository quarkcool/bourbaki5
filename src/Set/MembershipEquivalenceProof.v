Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Set.Syntax.

#[local] Set Typeclasses Unique Instances.
Class MembershipEquivalenceProof
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} X 𝐑 :=
proof : ⊢ ∀ x, x ∈ X ⇔ 𝐑 x.

Arguments proof {_ _ _ _}.