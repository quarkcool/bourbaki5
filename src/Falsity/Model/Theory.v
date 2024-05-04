Require Export
  Bourbaki.Falsity.Syntax
  Bourbaki.Formal.Model.Meta.StrongerTheoryEssence
  Bourbaki.Formal.Model.Meta.TheoryFromSet.

Module Model.
  Module Falsity.
    Section Falsity.
      Context `{Falsity.Syntax}.

      Definition Theory : Theory := {¬⊥,}%mset.

      Class FalsityTheory 𝒯 := is_falsity_theory : 𝒯 ⊃ Theory.
    End Falsity.
  End Falsity.
End Model.
Export Model.Falsity (FalsityTheory, is_falsity_theory).

Hint Extern 0 (FalsityTheory ?𝒯) =>
  tryif is_evar 𝒯 then
    fail "Met evar"
  else
    notypeclasses refine (_ : 𝒯 ⊃ _) :
typeclass_instances.

Hint Immediate is_falsity_theory : typeclass_instances.