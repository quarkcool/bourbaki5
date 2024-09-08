Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Set.Syntax.

Section Element.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  Class IsElement x X := element_essence : ⊢ x ∈ X.

  Structure Element X := {
    set :> Term;
    membership : IsElement set X
  }.

  Canonical element {x X} (H₁ : IsElement x X) := {| set := x |}.
End Element.

Hint Extern 0 (IsElement _ _) => ltac:(eassumption) : typeclass_instances.