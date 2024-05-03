Require Export
  Bourbaki.Formal.Meta.TheoryEquivalence
  Bourbaki.Logic.Meta.SingleAxiomTheory
  Bourbaki.Logic.Results.Meta.ListConjunction.

Section SingleAxiomTheory.
  Context `(TruthTheory, !LogicalTheory 𝒯).

  #[export]
  Instance :
    LogicalTheory (SingleAxiomTheory 𝒯).
  Proof.
    split.
    { Intros 𝐀 []. }
    { simpl.
      Apply StrongerTheoryEssence.weaker_schema. }
  Defined.

  Theorem equivalence :
    𝒯 ⟪⟫ SingleAxiomTheory 𝒯.
  Proof.
    split.
    { split.
      { Intros 𝐀 [H₁ | []].
        rewrite H₁.
        Apply ListConjunction.introduction.
        Apply @Proof.explicit_axiom. }
      { Intros 𝐀.
        Apply id. } }
    { split.
      { Intros 𝐀 H₁.
        Apply ListConjunction.elimination.
        { Apply Proof.explicit_axiom.
          left.
          Reflexivity. }
        { Assumption. } }
      { Intros 𝐀.
        Apply id. } }
  Defined.
End SingleAxiomTheory.