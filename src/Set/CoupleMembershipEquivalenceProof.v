Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Set.Term.Couple.

Class CoupleMembershipEquivalenceProof
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} X 𝐑 :=
proof : ⊢ ∀ x y, ❨x, y❩ ∈ X ⇔ 𝐑 x y.

Arguments proof {_ _ _ _}.