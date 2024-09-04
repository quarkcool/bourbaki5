Require Export
  Bourbaki.Formal.Theory.

Definition ImplicationProof `{Formal.Theory} 𝐑 𝐒 := ⊢ 𝐑 ⇒ 𝐒.
Hint Transparent ImplicationProof : entailment_instances.
Hint Transparent ImplicationProof : introduction_pattern_instances.

Infix "⊢⇒" := ImplicationProof : type_scope.