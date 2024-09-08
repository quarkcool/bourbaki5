Require Export
  Bourbaki.Set.Syntax.

Definition non_membership `{Set_.Syntax} x X := ¬x ∈ X.

Infix "∉" := non_membership : bourbaki_scope.