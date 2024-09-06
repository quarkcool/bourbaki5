Require Export
  Bourbaki.Formal.Relation.Implication
  Bourbaki.Logic.Relation.Conjunction.

(* équivalence *)
Definition equivalence `{Formal.Syntax} 𝐀 𝐁 := (𝐀 ⇒ 𝐁) ∧ (𝐁 ⇒ 𝐀).

Infix "⇔" := equivalence : bourbaki_scope.