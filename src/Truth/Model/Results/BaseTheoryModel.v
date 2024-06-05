Require Export
  Bourbaki.Formal.Model.Results.BaseTheoryModel
  Bourbaki.Truth.Model.Theory
  Bourbaki.Truth.Theory.

Section BaseTheoryModel.
  Context `{TruthTheory}.

  #[export]
  Instance :
    Truth.Theory (H1 := BaseTheoryModel.Th).
  Proof.
    split.
    { Apply StrongerTheoryEssence.weaker_explicit_axiom.
      constructor. }
  Defined.
End BaseTheoryModel.