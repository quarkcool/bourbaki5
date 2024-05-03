Require Export
  Bourbaki.Formal.Model.Meta.TheoryWithoutSomeAxioms
  Bourbaki.Formal.Model.Results.Meta.TheoryAdjunction
  Bourbaki.Formal.Model.Results.Meta.TheoryUnion
  Bourbaki.Logic.Model.Results.CanonicalModel
  Bourbaki.Logic.Results.Meta.Proof.

Section Proof.
  Context `{LogicalTheory}.

  (* C19 *)
  Theorem auxiliary_constant {𝐀 x 𝐁} :
    𝒯 ⊢ 𝐀 x -> (forall x : Term, 𝐀 x ∷ 𝒯 ⊢ 𝐁) -> 𝒯 ⊢ 𝐁.
  Proof.
    Intros H₁ H₂.
    Rewrite (TheoryAdjunction.absorption (𝐀 := 𝐀 x));
      Assumption.
  Defined.

  (* critère de la déduction / C14 *)
  Theorem deduction {𝐀 𝐁} :
    𝐀 ∷ 𝒯 ⊢ 𝐁 -> 𝒯 ⊢ 𝐀 ⇒ 𝐁.
  Proof.
    Intros H₁.
    induction H₁ as [𝐁 [H₁ | H₁] | 𝐁 [[] | H₁] | 𝐁 𝐂 _ IH₁ _ IH₂].
    { rewrite H₁.
      Reflexivity. }
    { Assumption. }
    { Assumption. }
    { Apply Implication.double_condition; simpl.
      Rewrite IH₂ at 1.
      Rewrite IH₁. }
  Defined.

  (* méthode de l'hypothèse auxiliaire *)
  Definition auxiliary_hypothesis_introduction_pattern 𝐀 𝐁 :
    IntroductionPattern simple_pattern (𝒯 ⊢ 𝐀 ⇒ 𝐁).
  Proof.
    refine '{| Intros.NewGoals := 𝐀 ∷ 𝒯 ⊢ 𝐀 -> 𝐀 ∷ 𝒯 ⊢ 𝐁 |}.
    Intros H₁.
    Apply Proof.deduction.
    Apply H₁.
    Apply Proof.explicit_axiom.
    left.
    Reflexivity.
  Defined.
End Proof.

Hint Extern 0 (IntroductionPattern _ _) =>
  notypeclasses refine (auxiliary_hypothesis_introduction_pattern _ _) :
introduction_pattern_instances.

Section Proof.
  Context `{LogicalTheory}.

  Definition deduction₂ {𝐀 𝐁} :
    𝒯 ⊢ 𝐁 -> 𝒯 \ {𝐀,} ⊢ 𝐀 ⇒ 𝐁.
  Proof.
    Intros H₁.
    Apply Proof.deduction.
    Rewrite TheoryUnion.commutativity.
    Rewrite (_ : 𝒯 \ {𝐀,} ∪ {𝐀,}%mset ⊃ 𝒯 ∪ {𝐀,}%mset).
    { Apply StrongerTheoryEssence.from_inclusions.
      Apply Set_.union_with_difference_left. }
    { Assumption. }
  Defined.

  (* C15 *)
  Theorem reductio_ad_absurdum {𝐀} :
    Contradiction (H0 := CanonicalModel.Th (𝒯 := (¬𝐀) ∷ 𝒯)) -> 𝒯 ⊢ 𝐀.
  Proof.
    Intros H₁.
    Apply Logic.disjunction_idempotence.
    Rewrite <- (_ : ¬𝐀 ⊢⇒ 𝐀) at 2.
    { Intros H₂.
      Apply Negation.ex_falso_quodlibet.
      Assumption. }
    { Apply Disjunction.excluded_middle. }
  Defined.

  (* méthode de réduction à l'absurde *)
  Definition reductio_ad_absurdum_introduction_pattern
    𝐀 (𝐁 : SolveLater Relation) :
      IntroductionPattern fresh_pattern (𝒯 ⊢ 𝐀).
  Proof.
    refine '{|
      Intros.NewGoals :=
        (¬𝐀) ∷ 𝒯 ⊢ ¬𝐀 -> ((¬𝐀) ∷ 𝒯 ⊢ 𝐁) * ((¬𝐀) ∷ 𝒯 ⊢ ¬𝐁)
    |}.
    Intros H₁.
    Apply Proof.reductio_ad_absurdum;
    do 2 esplit >
      [Apply Datatypes.fst | Apply Datatypes.snd];
      Apply H₁;
      Apply Proof.explicit_axiom;
      left;
      Reflexivity.
  Defined.
End Proof.

Hint Resolve reductio_ad_absurdum_introduction_pattern | 0 :
introduction_pattern_instances.