Require Export
  Bourbaki.Set.Relation.NonMembership
  Bourbaki.Set.Term.CollectivizingSubset
  Bourbaki.Set.Term.Subset.

(* Def_E_II_1__3 / complémentaire de A par rapport à X *)
Definition complement
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} X (A : Subset X) :=
{x ∈ X | x ∉ A}.

Notation "∁" := complement : bourbaki_scope.