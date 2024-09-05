Require Export
  Bourbaki.Formal.Contradiction
  Bourbaki.Logic.Results.Meta.Disjunction
  Bourbaki.Meta.Tactic.Exfalso.

Section Logic.
  Context `{Logic.Theory}.

  Theorem ex_falso_quodlibet 𝐑 :
    Contradiction -> ⊢ 𝐑.
  Proof.
    Intros [𝐒 [H₁ H₂]].
    Apply (_ : ⊢ 𝐒 ⇒ 𝐑);
      Assumption.
  Qed.

  #[export]
  Instance :
    forall 𝐑, ExfalsoRule (⊢ 𝐑).
  Proof.
    Intros 𝐑.
    esplit.
    Apply Logic.ex_falso_quodlibet.
  Defined.

  (* C10 *)
  Theorem excluded_middle 𝐑 :
    ⊢ 𝐑 ∨ ¬𝐑.
  Proof.
    Apply Logic.disjunction_symmetry.
    Apply Implication.reflexivity.
  Qed.

  (* C15 / réduction à l'absurde *)
  Theorem reductio_ad_absurdum {𝐑} :
    ((⊢ ¬𝐑) -> Contradiction) -> ⊢ 𝐑.
  Proof.
    Intros H₁.
    Apply Logic.disjunction_idempotence.
    Rewrite <- (_ : ¬𝐑 ⊢⇒ 𝐑) at 2.
    { Intros H₂.
      Exfalso.
      Apply H₁.
      Assumption. }
    { Apply Logic.excluded_middle. }
  Qed.

  Fact absurd_introduction_pattern 𝐑 :
    IntroductionPattern fresh_pattern (⊢ 𝐑).
  Proof.
    esplit.
    Apply Logic.reductio_ad_absurdum.
  Defined.

  (* C19 / constante auxiliaire *)
  Theorem auxiliary_constant (𝐑 : Formal.Term -> _) 𝐒 x :
    (⊢ 𝐑 x) -> (forall x, (⊢ 𝐑 x) -> ⊢ 𝐒) -> ⊢ 𝐒.
  Proof.
    Intros H₁ H₂.
    Apply H₂.
    Assumption.
  Qed.

  Theorem excluded_middle_elimination {𝐑 𝐒} :
    (⊢ 𝐑 ⇒ 𝐒) -> (⊢ ¬𝐑 ⇒ 𝐒) -> ⊢ 𝐒.
  Proof.
    Intros H₁ H₂.
    Apply Disjunction.elimination.
    { Apply Logic.excluded_middle. }
    all: Assumption.
  Qed.
End Logic.

Hint Resolve absurd_introduction_pattern | 0 : introduction_pattern_instances.