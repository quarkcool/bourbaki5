Require Export
  Bourbaki.Formal.Model.Theory.

Definition TheoryWithoutSomeAxioms `(𝒯 : Theory) 𝐀s :=
{|
  Theory.ExplicitAxioms := 𝒯.(ExplicitAxioms) \ 𝐀s;
  Theory.Schemas := 𝒯.(Schemas)
|}.

Infix "\" := TheoryWithoutSomeAxioms : bourbaki_theory_scope.