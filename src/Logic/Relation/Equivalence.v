Require Export
  Bourbaki.Formal.Relation.Implication
  Bourbaki.Logic.Relation.Conjunction.

(* équivalence *)
Definition equivalence `{Formal.Syntax} 𝐀 𝐁 := (𝐀 ⇒ 𝐁) ∧ (𝐁 ⇒ 𝐀).
Hint Transparent equivalence : introduction_pattern_instances.

Infix "⇔" := equivalence : bourbaki_scope.