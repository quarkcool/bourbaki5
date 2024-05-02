Require Export
  Bourbaki.Formal.Model.Meta.StrongerTheoryEssence.

(* théories équivalentes *)
Class TheoryEquivalence `{Formal.Syntax} 𝒯₁ 𝒯₂ := {
  left_to_right : 𝒯₁ ⊃ 𝒯₂;
  right_to_left : 𝒯₂ ⊃ 𝒯₁
}.

Infix "⊃⊂" := TheoryEquivalence : type_scope.