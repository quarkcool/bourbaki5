Require Export
  Bourbaki.Formal.Model.Results.CanonicalModel
  Bourbaki.Formal.Model.Results.Meta.Proof
  Bourbaki.Logic.CoreTheory
  Bourbaki.Logic.Model.Theory.

Section CanonicalModel.
  Context `{LogicalTheory}.

  #[export]
  Instance :
    Logic.CoreTheory (H0 := CanonicalModel.Th).
  Proof.
    split;
      intros;
      Apply StrongerTheoryEssence.weaker_schema;
      constructor.
  Defined.
End CanonicalModel.