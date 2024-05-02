Require Export
  Bourbaki.Formal.Model.Meta.TheoryFromSet
  Bourbaki.Formal.Model.Meta.TheoryUnion
  Bourbaki.Formal.Model.Proof.

Structure ProofInBaseTheory `{𝒯 : Theory} 𝐀 := {
  AdjoinedAxioms : Set_ Relation;
  AdjoinedAxioms_decidable_membership :: DecidableMembership AdjoinedAxioms;

  proof : AdjoinedAxioms ∪ 𝒯 ⊢ 𝐀
}.

Arguments AdjoinedAxioms {_ _ _}.
Arguments proof {_ _ _}.