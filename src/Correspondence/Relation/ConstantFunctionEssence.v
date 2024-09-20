Require Export
  Bourbaki.Correspondence.Term.Value.

(* f est [une fonction] constante *)
Definition is_constant_function
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} {X Y} (f : X → Y) :=
∀ x₁ x₂ ⟨∈ X⟩, f x₁ = f x₂.