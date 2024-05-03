Require Export
  Bourbaki.Formal.Syntax
  Bourbaki.Logic.Notation.

(* conjonction *)
Definition conjunction `{Formal.Syntax} 𝐀 𝐁 := ¬(¬𝐀 ∨ ¬𝐁).

Infix "∧" := conjunction : bourbaki_scope.