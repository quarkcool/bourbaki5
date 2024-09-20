Require Export
  Bourbaki.Correspondence.Relation.CorrespondenceEssence
  Bourbaki.Correspondence.Relation.FunctionalGraphEssence.

Section FunctionEssence.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  (*
    Def_E_II_3__9_ii /
    être une fonction entre un ensemble X et un ensemble Y /
    être une famille d'éléments de Y
  *)
  Definition is_function F X Y :=
  is_correspondence F X Y ∧ is_functional_graph F ∧ X = pr₁⟨F⟩.

  #[local] Set Typeclasses Unique Instances.
  Class IsFunction F X Y := function_essence : ⊢ is_function F X Y.
End FunctionEssence.

Hint Extern 0 (⊢ is_function _ _ _) =>
  notypeclasses refine function_essence :
typeclass_instances.