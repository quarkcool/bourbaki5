Require Export
  Bourbaki.Formal.Syntax.

Definition implication `{Formal.Syntax} 𝐀 𝐁 := ¬𝐀 ∨ 𝐁.

Infix "⇒" := implication : bourbaki_scope.