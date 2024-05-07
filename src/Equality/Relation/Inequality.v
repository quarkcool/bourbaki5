Require Export
  Bourbaki.Equality.Syntax.

Definition inequality `{Equality.Syntax} x y := ¬x = y.

Infix "≠" := inequality : bourbaki_scope.