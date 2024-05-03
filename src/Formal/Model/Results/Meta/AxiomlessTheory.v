Require Export
  Bourbaki.Formal.Model.Meta.AxiomlessTheory
  Bourbaki.Logic.Model.Results.BaseTheoryModel
  Bourbaki.Logic.Results.Meta.ListConjunction
  Bourbaki.Truth.Model.Theory.

Section AxiomlessTheory.
  Context `{TruthTheory, !LogicalTheory 𝒯, !TruthTheory (AxiomlessTheory 𝒯)}.

  Theorem axiom_removal {𝐀} :
    let P :=
      fun 𝐀s =>
        (
          (forall 𝐀, List.InT 𝐀 𝐀s -> 𝐀 ∈ 𝒯.(ExplicitAxioms)) *
            (AxiomlessTheory 𝒯 ⊢ list_conjunction 𝐀s ⇒ 𝐀)
        )%type
    in
    CRelationClasses.iffT (𝒯 ⊢ 𝐀) {𝐀s & P 𝐀s}.
  Proof.
    split.
    { Intros H₁.
      induction H₁
        as [𝐀 H₁ | 𝐀 H₁ | 𝐀 𝐁 _ [𝐀s₁ [IH₁ IH₂]] _ [𝐀s₂ [IH₃ IH₄]]].
      { exists [𝐀].
        split.
        { Intros 𝐁 [H₂ | []].
          rewrite H₂.
          Assumption. }
        { Intros H₂.
          Apply H₂.
          cbv -[Set_.union_with_difference_left].
          Change (_ ∪ (_ ∪ _ \ _) ⊂ _).
          (*Arguments entails : clear implicits.*)
          Qed. } }
      { exists [].
        split.
        { Intros 𝐁 []. }
        { Intros _.
          Apply Proof.implicit_axiom.
          Assumption. } }
      { exists ((𝐀s₁ ++ 𝐀s₂)%list).
        split.
        { Intros 𝐂 H₁.
          destruct (List.InT_app_or H₁) as [|];
            plus [Apply IH₁ | Apply IH₃];
            Assumption. }
        { Intros H₁.
          Apply IH₄.
          { Apply ListConjunction.concatenation_elimination.
            Assumption. }
          { Apply IH₂.
            Apply ListConjunction.concatenation_elimination;
            Assumption. } } } }
    { Intros [𝐀s [H₁ H₂]].
      Apply H₂.
      Apply ListConjunction.introduction.
      Intros 𝐁 H₃.
      Apply H₁.
      Assumption. }
  Defined.

  Let P :=
  fun 𝐀s =>
    (
      (forall 𝐀, List.InT 𝐀 𝐀s -> List.InT 𝐀 𝒯.(explicit_axioms)) *
        (AxiomlessTheory 𝒯 ⊢ ¬list_conjunction 𝐀s)
    )%type.

  Theorem contradiction_impact₁ :
    Contradictory 𝒯 -> {𝐀s & P 𝐀s}.
  Proof.
    Intros [𝐀 [H₁ H₂]].
    assert (H₃ : 𝒯 ⊢ 𝐀 ∧ ¬𝐀).
    { Intros [|];
        Assumption. }
    { destruct (fst axiom_removal H₃) as [𝐀s [H₄ H₅]].
      do 2 esplit.
      { Assumption. }
      { Rewrite H₅.
        Apply Conjunction.contradiction_impossibility. } }
  Defined.

  Theorem contradiction_impact₂ :
    {𝐀s & P 𝐀s} -> Contradictory 𝒯.
  Proof.
    Intros [𝐀s [H₁ H₂]].
    do 2 esplit.
    { Apply ListConjunction.introduction.
      Intros 𝐀 H₃.
      Apply H₁.
      Assumption. }
    { Assumption. }
  Defined.
End AxiomlessTheory.