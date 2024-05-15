Require Export
  Bourbaki.Set.Syntax.

Definition non_membership `{Set_.Syntax} x y := ¬x ∈ y.

Infix "∉" := non_membership : bourbaki_scope.