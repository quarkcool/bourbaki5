Require Export
  Bourbaki.Formal.Theory.

Definition ConditionalMetaRelation `{Formal.Theory} 𝐀 f :=
fun 𝐁 𝐂 : Relation => ⊢ 𝐀 ⇒ f 𝐁 𝐂.
Hint Transparent ConditionalMetaRelation : introduction_pattern_instances.