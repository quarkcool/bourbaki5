Require Export
  Bourbaki.Correspondence.Term.GraphProjections
  Bourbaki.Set.Relation.Inclusion.

Section CorrespondenceEssence.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  (* Def_E_II_3__2 / correspondance entre un ensemble X et un ensemble Y *)
  Definition is_correspondence G X Y := pr₁⟨G⟩ ⊂ X ∧ pr₂⟨G⟩ ⊂ Y.

  #[local] Set Typeclasses Unique Instances.
  Class IsCorrespondence G X Y :=
  correspondence_essence : ⊢ is_correspondence G X Y.
End CorrespondenceEssence.

Hint Extern 0 (IsCorrespondence _ _ _) => eassumption : typeclass_instances.

Hint Extern 0 (⊢ is_correspondence _ _ _) =>
  notypeclasses refine correspondence_essence :
typeclass_instances.