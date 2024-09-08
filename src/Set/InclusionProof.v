Require Export
  Bourbaki.Formal.CoercibleTerm
  Bourbaki.Formal.Theory
  Bourbaki.Set.Relation.Inclusion.

Class InclusionProof
  `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}
  {T : CoercibleTerm} (x y : T) :=
proof : ⊢ x ⊂ y.
Hint Transparent InclusionProof : typeclass_instances.

Infix "⊢⊂" := InclusionProof : type_scope.

Hint Extern 0 (_ ⊢⊂ _) => eassumption : typeclass_instances.