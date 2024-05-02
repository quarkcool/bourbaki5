Require Export
  Bourbaki.Formal.Relation.Implication.

Module Formal.
  Class Theory `{Formal.Syntax} := {
    Proof : Relation -> Type where "⊢ 𝐀" := (Proof 𝐀);

    #[canonical=no] syllogism :
      forall {𝐀 𝐁}, ⊢ 𝐀 -> ⊢ 𝐀 ⇒ 𝐁 -> ⊢ 𝐁
  }.
End Formal.

Notation "⊢ 𝐀" := (Formal.Proof 𝐀) : type_scope.