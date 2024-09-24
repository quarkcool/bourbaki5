Require Export
  Bourbaki.Correspondence.Term.Value
  Bourbaki.Equality.Relation.Inequality.

Section Injectivity.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  (*
    Def_E_II_3__10_i /
    f est une injection /
    f est [une application] injective /
    f est biunivoque
  *)
  Definition is_injective {X Y} (f : X → Y) :=
  ∀ x₁ x₂ ⟨∈ X⟩, x₁ ≠ x₂ ⇒ f x₁ ≠ f x₂.

  #[local] Set Typeclasses Unique Instances.
  Class IsInjective {X Y} (f : X → Y) := injectivity : ⊢ is_injective f.
End Injectivity.