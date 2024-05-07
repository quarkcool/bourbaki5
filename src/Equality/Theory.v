Require Export
  Bourbaki.Equality.Syntax
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Quantification.Theory.

Module Equality.
  Section Equality.
    Context `{Equality.Syntax}.

    Inductive Schemas : Relation -> Type :=
    (* S6 *)
    | equals_indiscernibility :
      forall x y 𝐑, Schemas (x = y ⇒ (𝐑 x ⇔ 𝐑 y))
    (* S7 *)
    | tau_rewriting :
      forall 𝐑 𝐒, Schemas ((∀ x, 𝐑 x ⇔ 𝐒 x) ⇒ (τ x, 𝐑 x) = τ x, 𝐒 x).

    Canonical Theory :=
    {| Theory.explicit_axioms := []; Theory.Schemas := Schemas |}.

    (* théorie égalitaire *)
    Class EqualitarianTheory {𝒯} `{!LogicalTheory 𝒯, !QuantifiedTheory} :=
    is_equalitarian_theory : 𝒯 ⟫ Theory.
  End Equality.
End Equality.
Export (canonicals) Equality.
Export Equality (EqualitarianTheory, is_equalitarian_theory).

Hint Extern 0 (EqualitarianTheory (𝒯 := ?𝒯)) =>
  tryif is_evar 𝒯 then
    fail "Met evar"
  else
    notypeclasses refine (_ : 𝒯 ⟫ _) :
typeclass_instances.

Hint Immediate is_equalitarian_theory : typeclass_instances.