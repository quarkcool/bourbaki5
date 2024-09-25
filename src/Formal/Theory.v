Require Export
  Bourbaki.Formal.Relation.Implication.

Module Formal.
  Class Theory `{Formal.Syntax} := {
    (* démonstration *)
    Proof : Relation -> Prop where "⊢ 𝐀" := (Proof 𝐀);

    (* C1 / syllogisme *)
    syllogism : forall {𝐀 𝐁}, (⊢ 𝐀) -> (⊢ 𝐀 ⇒ 𝐁) -> ⊢ 𝐁
  }.
End Formal.

Notation "⊢ 𝐀" := (Formal.Proof 𝐀) : bourbaki_scope.