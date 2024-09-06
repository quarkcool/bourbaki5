Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Logic.Relation.Equivalence.

Definition EquivalenceProof `{Formal.Theory} 𝐀 𝐁 := ⊢ 𝐀 ⇔ 𝐁.

Infix "⊢⇔" := EquivalenceProof : type_scope.