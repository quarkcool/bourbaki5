Require Export
  Bourbaki.Formal.Model.Results.BaseTheoryModel
  Bourbaki.Logic.Model.Results.Meta.Proof.

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

  Definition LogicTh :
    Logic.Theory.
  Proof.
    split.
    { Intros 𝐀 𝐁 H₁.
      assert (H₂ : ⊢ 𝐀).
      { Apply {| ProofInBaseTheory.AdjoinedAxioms := {𝐀,} |}.
        Apply Proof.explicit_axiom.
        left.
        Reflexivity. }
      { Apply {|
          ProofInBaseTheory.AdjoinedAxioms := (H₁ H₂).(AdjoinedAxioms) \ {𝐀,}
        |}.
        Rewrite (_ :
          (H₁ H₂).(AdjoinedAxioms) \ {𝐀,} ∪ 𝒯 ⊃
            (H₁ H₂).(AdjoinedAxioms) ∪ 𝒯 \ {𝐀,}
        ).
        { Apply StrongerTheoryEssence.from_inclusions.
          Apply Set_.difference_from_union. }
        { Apply Proof.deduction₂.
          Apply ProofInBaseTheory.proof. } } }
  Defined.
End BaseTheoryModel.

Hint Extern 0 (Logic.Theory) =>
  notypeclasses refine LogicTh :
typeclass_instances.