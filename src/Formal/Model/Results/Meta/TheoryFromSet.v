Require Export
  Bourbaki.Formal.Model.Meta.TheoryFromSet
  Bourbaki.Formal.Model.Results.Meta.StrongerTheoryEssence.

Section TheoryFromSet.
  Context `{Formal.Syntax}.

  #[export]
  Instance :
    CMorphisms.Proper (Inclusion --> StrongerTheoryEssence) TheoryFromSet.
  Proof.
    Intros 𝐀s₂ 𝐀s₁ H₁; unfold CRelationClasses.flip in *.
    typeclasses_eauto.
  Defined.
End TheoryFromSet.