Require Export
  Bourbaki.Logic.Theory
  Bourbaki.Quantification.Relation.Existence.

Module Quantification.
  Section Quantification.
    Context `{Formal.Syntax}.

    Inductive Schemas : Relation -> Type :=
    (* S5 *)
    | existence_introduction : forall 𝐑 x, Schemas (𝐑 x ⇒ ∃ x, 𝐑 x).

    Canonical Theory :=
    {| Theory.explicit_axioms := []; Theory.Schemas := Schemas |}.

    (* théorie quantifiée *)
    Class QuantifiedTheory {𝒯} `{!LogicalTheory 𝒯} :=
    is_quantified_theory : 𝒯 ⟫ Theory.
  End Quantification.
End Quantification.
Export (canonicals) Quantification.
Export Quantification (QuantifiedTheory, is_quantified_theory).

Hint Extern 0 (QuantifiedTheory (𝒯 := ?𝒯)) =>
  tryif is_evar 𝒯 then
    fail "Met evar"
  else
    notypeclasses refine (_ : 𝒯 ⟫ _) :
typeclass_instances.

Hint Immediate is_quantified_theory : typeclass_instances.