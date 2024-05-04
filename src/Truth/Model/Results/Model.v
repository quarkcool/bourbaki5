Require Export
  Bourbaki.Formal.Model.Results.CanonicalModel
  Bourbaki.Truth.Model.Theory
  Bourbaki.Truth.Theory.

Section Model.
  Context `{TruthTheory}.

  #[export]
  Instance :
    Truth.Theory.
  Proof.
    split.
    { Apply StrongerTheoryEssence.weaker_explicit_axiom.
      constructor. }
  Defined.
End Model.