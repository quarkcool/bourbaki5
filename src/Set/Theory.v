Require Export
  Bourbaki.Equality.Theory
  Bourbaki.Set.Syntax.

Module Set_.
  #[warnings="-non-primitive-record"]
  Class Theory `{Equality.Theory, !Set_.Syntax}.
End Set_.