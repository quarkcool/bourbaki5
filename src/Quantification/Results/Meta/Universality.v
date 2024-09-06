Require Export
  Bourbaki.Logic.Results.Meta.All
  Bourbaki.Logic.Results.Negation
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Quantification.Results.Meta.Existence.

Module Universality.
  Section Universality.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    (* C26 *)
    Theorem alternative_definition 𝐑 :
      ⊢ (∀ x, 𝐑 x) ⇔ 𝐑 (τ x, ¬𝐑 x).
    Proof.
      unfold universality.
      Rewrite Existence.definition.
      Apply Negation.double_removalₑ.
    Qed.

    (* C27 *)
    Theorem introduction 𝐑 :
      (forall x, ⊢ 𝐑 x) -> ⊢ ∀ x, 𝐑 x.
    Proof.
      Intros H₁.
      Apply Universality.alternative_definition.
      Assumption.
    Qed.

    Fact introduction_pattern 𝐑 :
      IntroductionPattern simple_pattern (⊢ ∀ x, 𝐑 x).
    Proof.
      esplit.
      Apply Universality.introduction.
    Defined.
  End Universality.

  Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.
End Universality.
Export (hints) Universality.