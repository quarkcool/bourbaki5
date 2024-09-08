Require Export
  Bourbaki.Equality.Theory
  Bourbaki.Set.Relation.Inclusion.

Module Set_.
  Class Theory `{Equality.Theory, !Set_.Syntax} := {
    (* A1 *)
    extensionality :
      ⊢ ∀ x y, x ⊂ y ⇒ y ⊂ x ⇒ x = y
  }.
End Set_.