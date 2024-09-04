Require Export
  Bourbaki.Formal.Syntax.

Section CoercibleTerm.
  Context `{Formal.Syntax}.

  Structure CoercibleTerm := {
    Type_ :> Type;
    coercion : Type_ -> Term
  }.

  Canonical Term_ := {| coercion := fun x => x |}.
End CoercibleTerm.

Coercion coercion : Type_ >-> Term.