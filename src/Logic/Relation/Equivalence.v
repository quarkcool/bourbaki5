Require Export
  Bourbaki.Formal.Relation.Implication
  Bourbaki.Logic.Relation.Conjunction.

(* équivalence *)
Definition equivalence `{Formal.Syntax} 𝐑 𝐒 := (𝐑 ⇒ 𝐒) ∧ (𝐒 ⇒ 𝐑).
Hint Transparent equivalence : entailment_instances.
Hint Transparent equivalence : introduction_pattern_instances.

Infix "⇔" := equivalence : bourbaki_scope.