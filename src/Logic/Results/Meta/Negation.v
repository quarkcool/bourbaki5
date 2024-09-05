Require Export
  Bourbaki.Logic.Results.Meta.Logic.

Module Negation.
  Section Negation.
    Context `{Logic.Theory, !Logic.Truth.Syntax}.

    Fact entailment {𝐀} {H₁ : SolveLater (⊢ 𝐀)} {H₂ : ⊢ ¬𝐀} :
      Entailment false H₂ (⊢ ⊥).
    Proof.
      repeat split.
      Apply Logic.ex_falso_quodlibet.
      repeat esplit;
        Assumption.
    Defined.
  End Negation.

  Hint Resolve entailment | 1 : entailment_instances.

  Section Negation.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    (* C11 *)
    Theorem double_removal 𝐀 :
      ⊢ 𝐀 ⇒ ¬¬𝐀.
    Proof.
      Apply Logic.excluded_middle.
    Qed.

    (* C12 *)
    Theorem rewriting 𝐀 𝐁 :
      ⊢ (𝐀 ⇒ 𝐁) ⇒ ¬𝐁 ⇒ ¬𝐀.
    Proof.
      Rewrite <- (Logic.disjunction_symmetry (¬𝐀)).
      Rewrite <- Negation.double_removal.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper (ImplicationProof --> ImplicationProof) negation
    | 0.
    Proof.
      Intros 𝐁 𝐀 H₁; unfold Basics.flip in *.
      Apply Negation.rewriting.
      Assumption.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (ImplicationProof ==> Basics.flip ImplicationProof)
        negation
    | 0 := ltac2:(flip_morphism ()).

    (* C16 *)
    Theorem doubling 𝐀 :
      ⊢ ¬¬𝐀 ⇒ 𝐀.
    Proof.
      Intros H₁ ?contra₁.
      Apply H₁.
      Assumption.
    Qed.

    Fact introduction_pattern
      {cat 𝐀}
      `(!Ununifiable cat fresh_pattern)
      `(pat : !IntroductionPattern cat (⊢ 𝐀 ⇒ ⊥)) :
        IntroductionPattern cat (⊢ ¬𝐀).
    Proof.
      esplit.
      Intros H₁ ?contra₁.
      Apply pat.(Intros.introduction_pattern).
      { Assumption. }
      { Apply Negation.doubling.
        Assumption. }
    Defined.
  End Negation.

  Hint Resolve introduction_pattern | 1 : introduction_pattern_instances.
End Negation.
Export (hints) Negation.