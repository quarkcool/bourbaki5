Require Export
  Bourbaki.Formal.Model.Meta.StrongerTheoryEssence
  Bourbaki.Formal.Model.Meta.TheoryFromSet
  Bourbaki.Truth.Syntax.

Module Model.
  Module Truth.
    Section Truth.
      Context `{Truth.Syntax}.

      Definition Theory : Theory := {⊤,}%mset.

      Class TruthTheory 𝒯 := is_truth_theory : 𝒯 ⊃ Theory.
    End Truth.
  End Truth.
End Model.
Export Model.Truth (TruthTheory, is_truth_theory).

Hint Extern 0 (TruthTheory ?𝒯) =>
  tryif is_evar 𝒯 then
    fail "Met evar"
  else
    notypeclasses refine (_ : 𝒯 ⊃ _) :
typeclass_instances.

Hint Immediate is_truth_theory : typeclass_instances.