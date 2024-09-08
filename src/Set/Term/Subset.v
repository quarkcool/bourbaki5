Require Export
  Bourbaki.Set.InclusionProof.

Section Subset.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  Structure Subset (x : Term) := {
    set :> Term;
    #[export, canonical=no] subset_essence :: set ⊢⊂ x
  }.
  Canonical Subset_ x := {| coercion := fun a => set x a |}.

  Canonical subset {a x} (H₁ : a ⊢⊂ x) := {| set := a |}.
End Subset.

Notation "↑ a" := (subset (a := a) _) : bourbaki_scope.