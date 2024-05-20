Require Export
  Bourbaki.Equality.Theory
  Bourbaki.Set.Relation.CollectivizingRelation
  Bourbaki.Set.Relation.Inclusion.

Module Set_.
  Section Set_.
    Context `{Set_.Syntax}.

    Canonical Theory :=
    {|
      Theory.explicit_axioms := [
        ∀ x y, x ⊂ y ⇒ y ⊂ x ⇒ x = y;
        ∀ x y, Coll (fun z => z = x ∨ z = y)
      ];
      Theory.Schemas := fun _ => False
    |}.

    (* théorie des ensembles *)
    Class SetTheory {𝒯}
      `{!LogicalTheory 𝒯, !QuantifiedTheory, !EqualitarianTheory} :=
    is_set_theory : 𝒯 ⟫ Theory.
  End Set_.
End Set_.
Export (canonicals) Set_.
Export Set_ (SetTheory, is_set_theory).

Hint Extern 0 (SetTheory (𝒯 := ?𝒯)) =>
  tryif is_evar 𝒯 then
    fail "Met evar"
  else
    notypeclasses refine (_ : 𝒯 ⟫ _) :
typeclass_instances.

Hint Immediate is_set_theory : typeclass_instances.