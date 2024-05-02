Require Export
  Bourbaki.Formal.Model.Meta.TheoryUnion
  Bourbaki.Formal.Model.Results.Meta.StrongerTheoryEssence.

Section TheoryUnion.
  Context `{Formal.Syntax}.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        StrongerTheoryEssence ==> StrongerTheoryEssence ==>
          StrongerTheoryEssence
      )
      TheoryUnion.
  Proof.
    Intros 𝒯₂ 𝒯₁ H₁ 𝒯₄ 𝒯₃ H₂.
    split.
    { Intros 𝐀 [H₃ | H₃];
        Assumption. }
    { typeclasses_eauto. }
  Defined.

  Definition commutativity 𝒯₂ 𝒯₁ :
    𝒯₂ ∪ 𝒯₁ ⊃ 𝒯₁ ∪ 𝒯₂.
  Proof.
    Apply StrongerTheoryEssence.from_inclusions;
      Apply Set_.union_commutativity.
  Defined.
End TheoryUnion.