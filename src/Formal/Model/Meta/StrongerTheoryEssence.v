Require Export
  Bourbaki.Formal.Model.Proof.

#[local] Set Typeclasses Unique Instances.
(* théorie plus forte *)
Class StrongerTheoryEssence `{Formal.Syntax} 𝒯₂ 𝒯₁ := {
  weaker_explicit_axiom : forall 𝐀, 𝐀 ∈ 𝒯₁.(ExplicitAxioms) -> 𝒯₂ ⊢ 𝐀;
  weaker_schema : 𝒯₁.(Schemas) ⊂ 𝒯₂.(Schemas)
}.

Infix "⊃" := StrongerTheoryEssence : type_scope.

Hint Extern 0 (Theory.Schemas _ ⊂ Theory.Schemas _) =>
  simpl;
  notypeclasses refine weaker_schema;
  trivial :
typeclass_instances.