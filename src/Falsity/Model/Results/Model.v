Require Export
  Bourbaki.Falsity.Model.Theory
  Bourbaki.Falsity.Theory
  Bourbaki.Formal.Model.Results.CanonicalModel.

Section Model.
  Context `{FalsityTheory}.

  #[export]
  Instance :
    Falsity.Theory.
  Proof.
    split.
    { Apply StrongerTheoryEssence.weaker_explicit_axiom.
      constructor. }
  Defined.
End Model.