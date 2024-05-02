Require Export
  Bourbaki.Formal.Theory.

Definition ImplicationMetaRelation `{Formal.Theory} 𝐀 𝐁 := ⊢ 𝐀 ⇒ 𝐁.
Hint Transparent ImplicationMetaRelation : introduction_pattern_instances.

Infix "⊢⇒" := ImplicationMetaRelation : type_scope.