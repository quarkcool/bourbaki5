Require Export
  Bourbaki.Logic.Relation.ListDisjunction
  Bourbaki.Logic.Results.Equivalence.

Module Disjunction.
  Section Disjunction.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem as_conditionₑ 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ∨ 𝐁 ⇒ 𝐂 ⇔ (𝐀 ⇒ 𝐂) ∧ (𝐁 ⇒ 𝐂).
    Proof.
      Intros [H₁ [H₂ | H₂] | H₁ [H₂ | H₂]];
        Apply H₁;
        Assumption.
    Qed.

    (* C24_xi *)
    Theorem distributivity_over_conjunction_left 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ∨ 𝐁 ∧ 𝐂 ⇔ (𝐀 ∨ 𝐁) ∧ 𝐀 ∨ 𝐂.
    Proof.
      Intros [[H₁ | H₁] [|] | [[H₁ | H₁] [H₂ | H₂]]];
        plus [() | Apply Conjunction.introduction];
          Assumption.
    Qed.

    Theorem distributivity_over_conjunction_right 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ∧ 𝐁) ∨ 𝐂 ⇔ (𝐀 ∨ 𝐂) ∧ 𝐁 ∨ 𝐂.
    Proof.
      Rewrite <- (Disjunction.commutativity 𝐂).
      Apply Disjunction.distributivity_over_conjunction_left.
    Qed.

    Theorem negationₑ 𝐀 𝐁 :
      ⊢ ¬(𝐀 ∨ 𝐁) ⇔ ¬𝐀 ∧ ¬𝐁.
    Proof.
      unfold conjunction.
      Rewrite Negation.double_removalₑ.
    Qed.
  End Disjunction.
End Disjunction.

Module Conjunction.
  Section Conjunction.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem as_conditionₑ 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ∧ 𝐁 ⇒ 𝐂 ⇔ 𝐀 ⇒ 𝐁 ⇒ 𝐂.
    Proof.
      unfold implication at 1.
      Rewrite Conjunction.negationₑ.
      Rewrite <- Disjunction.associativity.
    Qed.

    Theorem as_consequenceₑ 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ⇒ 𝐁 ∧ 𝐂 ⇔ (𝐀 ⇒ 𝐁) ∧ (𝐀 ⇒ 𝐂).
    Proof.
      Apply Disjunction.distributivity_over_conjunction_left.
    Qed.

    (* C24_x *)
    Theorem distributivity_over_disjunction_left 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ∧ 𝐁 ∨ 𝐂 ⇔ (𝐀 ∧ 𝐁) ∨ 𝐀 ∧ 𝐂.
    Proof.
      Intros [[H₁ [H₂ | H₂]] | [H₁ | H₁] [|]];
        plus [() | Apply Conjunction.introduction];
          Assumption.
    Qed.

    Theorem distributivity_over_disjunction_right 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ∨ 𝐁) ∧ 𝐂 ⇔ (𝐀 ∧ 𝐂) ∨ 𝐁 ∧ 𝐂.
    Proof.
      Rewrite <- (Conjunction.commutativity 𝐂).
      Apply Conjunction.distributivity_over_disjunction_left.
    Qed.
  End Conjunction.
End Conjunction.

Module Implication.
  Section Implication.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem condition_commutativity 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ⇒ 𝐁 ⇒ 𝐂 ⇔ 𝐁 ⇒ 𝐀 ⇒ 𝐂.
    Proof.
      Rewrite <- Conjunction.as_conditionₑ.
      Rewrite (Conjunction.commutativity 𝐀).
    Qed.

    Theorem negationₑ 𝐀 𝐁 :
      ⊢ ¬(𝐀 ⇒ 𝐁) ⇔ 𝐀 ∧ ¬𝐁.
    Proof.
      Rewrite (Disjunction.negationₑ (¬𝐀) 𝐁).
      Rewrite Negation.double_removalₑ.
    Qed.
  End Implication.
End Implication.

Module Negation.
  Section Negation.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Theorem as_conditionₑ 𝐀 𝐁 :
      ⊢ ¬𝐀 ⇒ 𝐁 ⇔ 𝐀 ∨ 𝐁.
    Proof.
      Rewrite <- (Negation.double_removalₑ 𝐀) at 2.
    Qed.
  End Negation.
End Negation.

Module Other.
  Section Other.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    Lemma C13 {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇒ 𝐁) -> ⊢ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ⇒ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_ii {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇔ 𝐁) -> ⊢ 𝐀 ⇒ 𝐂 ⇔ 𝐁 ⇒ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_iii {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇔ 𝐁) -> ⊢ 𝐂 ⇒ 𝐀 ⇔ 𝐂 ⇒ 𝐁.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_iv {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇔ 𝐁) -> ⊢ 𝐀 ∧ 𝐂 ⇔ 𝐁 ∧ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C23_v {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇔ 𝐁) -> ⊢ 𝐀 ∨ 𝐂 ⇔ 𝐁 ∨ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma C24_vi 𝐀 𝐁 :
      ⊢ 𝐀 ∨ 𝐁 ⇔ ¬(¬𝐀 ∧ ¬𝐁).
    Proof.
      Rewrite <- Disjunction.negationₑ.
      Rewrite Negation.double_removalₑ.
    Qed.

    Lemma C24_xii 𝐀 𝐁 :
      ⊢ 𝐀 ∧ ¬𝐁 ⇔ ¬(𝐀 ⇒ 𝐁).
    Proof.
      Rewrite (Implication.negationₑ 𝐀 𝐁).
    Qed.

    Lemma C24_xiii 𝐀 𝐁 :
      ⊢ 𝐀 ∨ 𝐁 ⇔ ¬𝐀 ⇒ 𝐁.
    Proof.
      unfold implication.
      Rewrite Negation.double_removalₑ.
    Qed.

    Lemma C25_i {𝐀} 𝐁 :
      (⊢ 𝐀) -> ⊢ 𝐀 ∧ 𝐁 ⇔ 𝐁.
    Proof.
      Intros H₁.
      Apply Conjunction.operand_removal_left.
      Assumption.
    Qed.

    Lemma C25_ii {𝐀} 𝐁 :
      (⊢ ¬𝐀) -> ⊢ 𝐀 ∨ 𝐁 ⇔ 𝐁.
    Proof.
      Intros H₁.
      Apply Disjunction.operand_removal_left.
      Assumption.
    Qed.

    Lemma Ex_E_I_3__1_i 𝐀 𝐁 :
      ⊢ 𝐀 ⇒ 𝐁 ⇒ 𝐀.
    Proof.
      Intros H₁ _.
      Assumption.
    Qed.

    Lemma Ex_E_I_3__1_ii 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ⇒ 𝐁) ⇒ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ⇒ 𝐂.
    Proof.
      Intros H₁ H₂.
      Transitivity;
        Assumption.
    Qed.

    Lemma Ex_E_I_3__1_iii 𝐀 𝐁 :
      ⊢ 𝐀 ⇒ ¬𝐀 ⇒ 𝐁.
    Proof.
      Intros H₁ H₂.
      Exfalso.
      Apply H₂.
      Assumption.
    Qed.

    Lemma Ex_E_I_3__1_iv 𝐀 𝐁 :
      ⊢ 𝐀 ∨ 𝐁 ⇔ (𝐀 ⇒ 𝐁) ⇒ 𝐁.
    Proof.
      unfold implication at 1.
      Rewrite (Implication.negationₑ 𝐀).
      Rewrite Disjunction.distributivity_over_conjunction_right.
      Rewrite (Conjunction.operand_removal_right (𝐀 ∨ 𝐁)).
      Intros _.
      Apply Logic.disjunction_symmetry.
      Apply Logic.excluded_middle.
    Qed.

    Lemma Ex_E_I_3__1_v 𝐀 𝐁 :
      ⊢ (𝐀 ⇔ 𝐁) ⇔ (𝐀 ∧ 𝐁) ∨ ¬𝐀 ∧ ¬𝐁.
    Proof.
      Rewrite Disjunction.distributivity_over_conjunction_left.
      Rewrite Disjunction.distributivity_over_conjunction_right.
      Rewrite <- (Conjunction.commutativity (𝐁 ∨ ¬𝐁)).
      Rewrite (fun 𝐀 𝐁 => Conjunction.operand_removal_left 𝐀 (𝐁 ∨ ¬𝐁)).
      { Rewrite <- (fun 𝐀 => Disjunction.commutativity (¬𝐀)). }
      all:
        Apply Logic.excluded_middle.
    Qed.

    Lemma Ex_E_I_3__1_vi 𝐀 𝐁 :
      ⊢ ¬(¬𝐀 ⇔ 𝐁) ⇔ 𝐀 ⇔ 𝐁.
    Proof.
      Rewrite (Other.Ex_E_I_3__1_v (¬𝐀)).
      Rewrite Negation.double_removalₑ.
      Rewrite (Disjunction.negationₑ (¬𝐀 ∧ 𝐁)).
      Rewrite Conjunction.negationₑ.
      Rewrite Negation.double_removalₑ.
      Rewrite <- (Disjunction.commutativity (¬𝐁)).
      Apply Equivalence.commutativity.
    Qed.

    Lemma Ex_E_I_3__1_vii 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ⇒ 𝐁 ∨ ¬𝐂 ⇔ 𝐂 ∧ 𝐀 ⇒ 𝐁.
    Proof.
      unfold implication at 2.
      Rewrite Conjunction.negationₑ.
      Rewrite <- Disjunction.associativity.
      Rewrite (Disjunction.commutativity (¬𝐂)).
      Rewrite <- Disjunction.associativity.
    Qed.

    Lemma Ex_E_I_3__1_viii 𝐀 𝐁 𝐂 :
      ⊢ 𝐀 ⇒ 𝐁 ∨ 𝐂 ⇔ 𝐁 ∨ (𝐀 ⇒ 𝐂).
    Proof.
      Rewrite Disjunction.associativity.
      Rewrite (Disjunction.commutativity (¬𝐀)).
    Qed.

    Lemma Ex_E_I_3__1_ix 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ⇒ 𝐁) ⇒ (𝐀 ⇒ 𝐂) ⇒ 𝐀 ⇒ 𝐁 ∧ 𝐂.
    Proof.
      Rewrite <- Conjunction.as_conditionₑ.
      Apply Conjunction.as_consequenceₑ.
    Qed.

    Lemma Ex_E_I_3__1_x 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ⇒ 𝐂) ⇒ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ∨ 𝐁 ⇒ 𝐂.
    Proof.
      Intros H₁ H₂ [H₃ | H₃];
        plus [Apply H₁ | Apply H₂];
        Assumption.
    Qed.

    Lemma Ex_E_I_3__1_xi 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ⇒ 𝐁) ⇒ 𝐀 ∧ 𝐂 ⇒ 𝐁 ∧ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma Ex_E_I_3__1_xii 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ⇒ 𝐁) ⇒ 𝐀 ∨ 𝐂 ⇒ 𝐁 ∨ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.

    Lemma Ex_E_I_3__3_i {𝐀s} :
      (Forall (fun 𝐀 => ⊢ ¬𝐀) (removelast 𝐀s) -> ⊢ last 𝐀s ⊥) ->
        ⊢ list_disjunction 𝐀s.
    Proof.
      Intros H₁.
      induction 𝐀s as [| 𝐀 𝐀s IH₁]; simpl in *.
      { Apply H₁.
        constructor. }
      { destruct 𝐀s as [| 𝐁 𝐀s].
        { Apply H₁.
          constructor. }
        { Destruct Logic.excluded_middle as [H₂ | H₂].
          { Apply Logic.disjunction_introduction_left.
            Assumption. }
          { Apply IH₁.
            Intros H₃.
            Apply H₁.
            constructor;
              Assumption. } } }
    Qed.
  End Other.

  Module AlternateDenial.
    Section AlternateDenial.
      Context `{Logic.Truth.Theory, !Logic.Theory}.

      Definition alternate_denial 𝐑 𝐒 := ¬𝐑 ∨ ¬𝐒.

      Infix "|" :=
        alternate_denial (at level 102, right associativity) :
      bourbaki_scope.

      Lemma Ex_E_I_3__4_i 𝐀 :
        ⊢ ¬𝐀 ⇔ 𝐀 | 𝐀.
      Proof.
        Rewrite Disjunction.idempotenceₑ.
      Qed.

      Lemma Ex_E_I_3__4_ii 𝐀 𝐁 :
        ⊢ 𝐀 ∨ 𝐁 ⇔ (𝐀 | 𝐀) | 𝐁 | 𝐁.
      Proof.
        unfold alternate_denial at 1.
        Rewrite <- AlternateDenial.Ex_E_I_3__4_i.
        Rewrite Negation.double_removalₑ.
      Qed.

      Lemma Ex_E_I_3__4_iii 𝐀 𝐁 :
        ⊢ 𝐀 ∧ 𝐁 ⇔ (𝐀 | 𝐁) | 𝐀 | 𝐁.
      Proof.
        Apply AlternateDenial.Ex_E_I_3__4_i.
      Qed.

      Lemma Ex_E_I_3__4_iv 𝐀 𝐁 :
        ⊢ 𝐀 ⇒ 𝐁 ⇔ 𝐀 | 𝐁 | 𝐁.
      Proof.
        unfold alternate_denial at 1.
        Rewrite <- AlternateDenial.Ex_E_I_3__4_i.
        Rewrite Negation.double_removalₑ.
      Qed.
    End AlternateDenial.
  End AlternateDenial.
End Other.