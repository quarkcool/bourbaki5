Require Export
  Bourbaki.Formal.Relation.Implication.

Module Formal.
  Class Theory `{Formal.Syntax} := {
    (* démonstration *)
    Proof : Formal.Relation -> Prop where "⊢ 𝐑" := (Proof 𝐑);

    (* C1 / syllogisme *)
    syllogism : forall {𝐑 𝐒}, (⊢ 𝐑) -> (⊢ 𝐑 ⇒ 𝐒) -> ⊢ 𝐒
  }.
End Formal.

Notation "⊢ 𝐑" := (Formal.Proof 𝐑) : bourbaki_scope.