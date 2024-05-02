Require Export
  Bourbaki.Formal.Model.Results.BaseTheoryModel
  Bourbaki.Logic.CoreTheory
  Bourbaki.Logic.Model.Theory.

Section BaseTheoryModel.
  Context `{LogicalTheory}.

  #[export]
  Instance :
    Logic.CoreTheory (H0 := BaseTheoryModel.Th).
  Proof.
    split;
      intros;
      Apply {| ProofInBaseTheory.AdjoinedAxioms := ∅ |};
      Apply (StrongerTheoryEssence.weaker_schema (𝒯₁ := Model.Logic.Theory));
      constructor.
  Defined.
End BaseTheoryModel.