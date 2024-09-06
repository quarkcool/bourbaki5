Require Export
  Bourbaki.Formal.Syntax
  Bourbaki.Logic.Notation.

(* conjonction *)
Definition conjunction `{Formal.Syntax} 𝐑 𝐒 := ¬(¬𝐑 ∨ ¬𝐒).

Infix "∧" := conjunction : bourbaki_scope.