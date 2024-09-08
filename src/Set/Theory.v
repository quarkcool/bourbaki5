Require Export
  Bourbaki.Equality.Theory
  Bourbaki.Quantification.Relation.TypicalExistence
  Bourbaki.Set.Relation.CollectivizingEssence
  Bourbaki.Set.Relation.Inclusion.

Module Set_.
  Class Theory `{Equality.Theory, !Set_.Syntax} := {
    (* A1 *)
    extensionality :
      ⊢ ∀ x y, x ⊂ y ⇒ y ⊂ x ⇒ x = y;
    (* A2 / axiome de l'ensemble à deux éléments *)
    two_element_set :
      ⊢ ∀ x y, Coll (fun z => z = x ∨ z = y);
    (* S8 / schéma de sélection et union *)
    selection_union :
      forall 𝐑,
        ⊢ (∀ y, ∃ X, ∀ x, 𝐑 x y ⇒ x ∈ X) ⇒
          ∀ Y, Coll (fun x => ∃ y ⟨∈ Y⟩, 𝐑 x y)
  }.
End Set_.