Require Export
  Bourbaki.Formal.Model.Theory.

Definition TheoryFromSet `{Formal.Syntax} 𝐀s :=
{| Theory.ExplicitAxioms := 𝐀s; Theory.Schemas := ∅ |}.

#[warnings="-uniform-inheritance"]
Coercion TheoryFromSet : Set_ >-> Theory.