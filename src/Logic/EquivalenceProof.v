Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Logic.Relation.Equivalence.

Definition EquivalenceProof `{Formal.Theory} 𝐑 𝐒 := ⊢ 𝐑 ⇔ 𝐒.
Hint Transparent EquivalenceProof : entailment_instances.
Hint Transparent EquivalenceProof : introduction_pattern_instances.

Infix "⊢⇔" := EquivalenceProof : type_scope.