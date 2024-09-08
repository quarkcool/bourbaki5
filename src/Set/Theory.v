Require Export
  Bourbaki.Equality.Theory
  Bourbaki.Set.Relation.CollectivizingEssence
  Bourbaki.Set.Relation.Inclusion.

Module Set_.
  Class Theory `{Equality.Theory, !Set_.Syntax} := {
    (* A1 *)
    extensionality :
      ⊢ ∀ x y, x ⊂ y ⇒ y ⊂ x ⇒ x = y;
    (* A2 / axiome de l'ensemble à deux éléments *)
    two_element_set :
      ⊢ ∀ x y, Coll (fun z => z = x ∨ z = y)
  }.
End Set_.