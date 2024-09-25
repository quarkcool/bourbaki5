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

    (* C10 *)
    Theorem excluded_middle 𝐀 :
      ⊢ 𝐀 ∨ ¬𝐀.
    Proof.
      Apply Logic.disjunction_symmetry.
      Apply Implication.reflexivity.
    Qed.

    (* C15 / réduction à l'absurde *)
    Theorem reductio_ad_absurdum {𝐀} :
      ((⊢ ¬𝐀) -> Contradiction) -> ⊢ 𝐀.
    Proof.
      Intros H₁.
      Apply Logic.disjunction_idempotence.
      Rewrite <- (_ : ¬𝐀 ⊢⇒ 𝐀) at 2.
      { Intros H₂.
        Apply Logic.ex_falso_quodlibet.
        Apply H₁.
        Assumption. }
      { Apply Logic.excluded_middle. }
    Qed.

    Fact absurd_introduction_pattern 𝐀 :
      IntroductionPattern fresh_pattern (⊢ 𝐀).
    Proof.
      esplit with (NewGoals := (⊢ ¬𝐀) -> ⊢ ⊥).
      Intros H₁.
      Apply Logic.reductio_ad_absurdum.
      Intros H₂.
      repeat esplit.
      { Apply Logic.Truth.truth_truth. }
      { Apply H₁.
        Assumption. }
    Defined.

    (* C19 / constante auxiliaire *)
    Theorem auxiliary_constant {𝐑 : Term -> _} {𝐀} x :
      (⊢ 𝐑 x) -> (forall x, (⊢ 𝐑 x) -> ⊢ 𝐀) -> ⊢ 𝐀.
    Proof.
      Intros H₁ H₂.
      Apply H₂.
      Assumption.
    Qed.

    Theorem excluded_middle_elimination {𝐀 𝐁} :
      (⊢ 𝐀 ⇒ 𝐁) -> (⊢ ¬𝐀 ⇒ 𝐁) -> ⊢ 𝐁.
    Proof.
      Intros H₁ H₂.
      Destruct Logic.excluded_middle as [|];
        Assumption.
    Qed.
  End Logic.

  Hint Resolve absurd_introduction_pattern | 0 : introduction_pattern_instances.
End Logic.
Export (hints) Logic.