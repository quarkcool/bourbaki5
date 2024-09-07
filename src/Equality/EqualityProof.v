Require Export
  Bourbaki.Equality.Syntax
  Bourbaki.Formal.CoercibleTerm
  Bourbaki.Formal.Theory.

Definition EqualityProof
  `{Formal.Theory, !Equality.Syntax} {T : CoercibleTerm} (x y : T) :=
⊢ x = y.

Infix "⊢=" := EqualityProof : type_scope.