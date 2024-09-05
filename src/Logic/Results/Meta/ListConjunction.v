Require Export
  Bourbaki.Logic.Relation.ListConjunction
  Bourbaki.Logic.Results.Meta.Conjunction.

Section ListConjunction.
  Context `{Logic.Truth.Theory, !Logic.Theory}.

  Theorem introduction {𝐀s} :
    Forall Formal.Proof 𝐀s -> ⊢ list_conjunction 𝐀s.
  Proof.
    Intros H₁.
    induction 𝐀s as [| 𝐀 𝐀s IH₁]; simpl.
    { Apply Logic.Truth.truth_truth. }
    { inversion H₁ as [| 𝐀' 𝐀s' H₂ H₃].
      Intros [|];
        plus [() | Apply IH₁];
        Assumption. }
  Qed.
End ListConjunction.