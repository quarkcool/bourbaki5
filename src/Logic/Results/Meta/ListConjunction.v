Require Export
  Bourbaki.Logic.Relation.ListConjunction
  Bourbaki.Logic.Results.Meta.Conjunction
  Bourbaki.Truth.Theory
  Bourbaki.Util.Lists.List.

Section ListConjunction.
  Context `{Truth.Theory, !Logic.CoreTheory, !Logic.Theory}.

  Theorem concatenation_elimination 𝐀s₁ 𝐀s₂ :
    ⊢ list_conjunction (𝐀s₁ ++ 𝐀s₂) ⇒
      list_conjunction 𝐀s₁ ∧ list_conjunction 𝐀s₂.
  Proof.
    induction 𝐀s₁ as [| 𝐀 𝐀s₁ IH₁].
    { Intros H₁ [|].
      { Apply Truth.truth_truth. }
      { Assumption. } }
    { Intros H₁ [[|] |] > [| Change (⊢ list_conjunction _) |].
      { Assumption. }
      all:
        Apply IH₁;
        Assumption. }
  Defined.

  Theorem elimination {𝐀s 𝐀} :
    ⊢ list_conjunction 𝐀s -> List.InT 𝐀 𝐀s -> ⊢ 𝐀.
  Proof.
    induction 𝐀s as [| 𝐁 𝐀s IH₁].
    { Intros _ []. }
    { Intros H₁ [H₂ | H₂].
      { rewrite H₂.
        Assumption. }
      { Apply IH₁;
          Assumption. } }
  Defined.

  Theorem introduction 𝐀s :
    (forall 𝐀, List.InT 𝐀 𝐀s -> ⊢ 𝐀) -> ⊢ list_conjunction 𝐀s.
  Proof.
    induction 𝐀s as [| 𝐀 𝐀s IH₁].
    { Intros _.
      Apply Truth.truth_truth. }
    { Intros H₁ [|] > [| Change (⊢ list_conjunction _)].
      { Apply H₁.
        left.
        Reflexivity. }
      { Apply IH₁.
        Intros 𝐁 H₂.
        Apply H₁.
        right.
        Assumption. } }
  Defined.
End ListConjunction.