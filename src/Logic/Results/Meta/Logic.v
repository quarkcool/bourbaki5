Require Export
  Bourbaki.Formal.Contradiction
  Bourbaki.Logic.Results.Meta.Disjunction
  Bourbaki.Logic.Truth.Theory
  Bourbaki.Meta.Tactic.Exfalso.

Module Logic.
  Section Logic.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem ex_falso_quodlibet 𝐀 :
      Contradiction -> ⊢ 𝐀.
    Proof.
      Intros [𝐁 [H₁ H₂]].
      Apply (_ : ⊢ 𝐁 ⇒ 𝐀);
        Assumption.
    Qed.

    #[export]
    Instance :
      forall 𝐀, ExfalsoRule (⊢ 𝐀).
    Proof.
      esplit.
      Intros H₁.
      Apply Logic.ex_falso_quodlibet.
      repeat esplit.
      { Apply Logic.Truth.truth_truth. }
      { Assumption. }
    Defined.
  End Logic.
End Logic.
Export (hints) Logic.