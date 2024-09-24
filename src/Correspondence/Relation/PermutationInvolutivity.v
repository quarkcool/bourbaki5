Require Export
  Bourbaki.Correspondence.Relation.SymmetricGraphEssence
  Bourbaki.Correspondence.Term.Permutation.

Definition is_involutive_permutation
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} {X} (f : Permutation X) :=
is_symmetric_graph f.