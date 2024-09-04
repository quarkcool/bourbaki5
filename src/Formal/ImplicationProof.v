Require Export
  Bourbaki.Formal.Theory.

Definition ImplicationProof `{Formal.Theory} 𝐀 𝐁 := ⊢ 𝐀 ⇒ 𝐁.

Infix "⊢⇒" := ImplicationProof : type_scope.