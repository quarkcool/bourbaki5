Require Export
  Bourbaki.Formal.Model.Theory.

Definition AxiomlessTheory `(𝒯 : Theory) :=
{| Theory.ExplicitAxioms := ∅; Theory.Schemas := 𝒯.(Schemas) |}.