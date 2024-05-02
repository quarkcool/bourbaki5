Require Export
  Bourbaki.Formal.Model.Meta.StrongerTheoryEssence.

Module Model.
  Module Logic.
    Section Logic.
      Context `{Formal.Syntax}.

      Inductive Schemas : Relation -> Prop :=
      (* S1 *)
      | disjunction_idempotence :
        forall 𝐀, Schemas (𝐀 ∨ 𝐀 ⇒ 𝐀)
      (* S2 *)
      | disjunction_introduction_left :
        forall 𝐀 𝐁, Schemas (𝐀 ⇒ 𝐀 ∨ 𝐁)
      (* S3 *)
      | disjunction_commutativity :
        forall 𝐀 𝐁, Schemas (𝐀 ∨ 𝐁 ⇒ 𝐁 ∨ 𝐀)
      (* S4 *)
      | disjunction_rewriting_right :
        forall 𝐀 𝐁 𝐂, Schemas ((𝐀 ⇒ 𝐁) ⇒ 𝐂 ∨ 𝐀 ⇒ 𝐂 ∨ 𝐁).

      Canonical Theory :=
      {| Theory.ExplicitAxioms := ∅; Theory.Schemas := Schemas |}.

      (* théorie logique *)
      Class LogicalTheory 𝒯 := is_logical_theory : 𝒯 ⊃ Theory.
    End Logic.
  End Logic.
End Model.
Export (canonicals) Model.Logic.
Export Model.Logic (LogicalTheory, is_logical_theory).

Hint Extern 0 (LogicalTheory ?𝒯) =>
  tryif is_evar 𝒯 then
    fail "Met evar"
  else
    notypeclasses refine (_ : 𝒯 ⊃ _) :
typeclass_instances.

Hint Immediate is_logical_theory : typeclass_instances.