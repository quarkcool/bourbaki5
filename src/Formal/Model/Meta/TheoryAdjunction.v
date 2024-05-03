Require Export
  Bourbaki.Formal.Model.Meta.TheoryFromSet
  Bourbaki.Formal.Model.Meta.TheoryUnion.

Definition TheoryAdjunction `{Formal.Syntax} 𝐀 𝒯 : Theory := {𝐀,}%mset ∪ 𝒯.

Infix "∷" := TheoryAdjunction : bourbaki_scope.