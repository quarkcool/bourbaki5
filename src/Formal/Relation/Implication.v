Require Export
  Bourbaki.Formal.Syntax.

Definition implication `{Formal.Syntax} 𝐑 𝐒 := ¬𝐑 ∨ 𝐒.
Hint Transparent implication : entailment_instances.

Infix "⇒" := implication : bourbaki_scope.