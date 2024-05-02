Require Export
  Bourbaki.Formal.Model.Theory.

Definition TheoryUnion `{Formal.Syntax} 𝒯₁ 𝒯₂ := {|
  Theory.ExplicitAxioms := 𝒯₁.(ExplicitAxioms) ∪ 𝒯₂.(ExplicitAxioms);
  Theory.Schemas := 𝒯₁.(Schemas) ∪ 𝒯₂.(Schemas)
|}.

Infix "∪" := TheoryUnion : bourbaki_theory_scope.