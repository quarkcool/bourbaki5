Require Export
  Bourbaki.Correspondence.Term.Value.

(* x est invariant par f *)
Definition is_invariant_element
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} {X Y} (f : X → Y) x :=
f x = x.