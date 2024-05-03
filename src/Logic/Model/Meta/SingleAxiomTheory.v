Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Logic.Relation.ListConjunction.

Definition SingleAxiomTheory `{Truth.Syntax} 𝒯 :=
{|
  Theory.explicit_axioms := [list_conjunction 𝒯.(explicit_axioms)];
  Theory.Schemas := 𝒯.(Schemas)
|}.