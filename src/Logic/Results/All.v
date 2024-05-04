Require Export
  Bourbaki.Logic.Results.Conjunction
  Bourbaki.Logic.Results.Disjunction.

Import Proof.TheoryHidingNotation.

Module Conjunction.
  Section Conjunction.
    Context `(LogicalTheory).

    (* C24_j *)
    Theorem distributivity_with_disjunction_left 𝐀 𝐁 𝐂 :
      𝒯 ⊢ 𝐀 ∧ (𝐁 ∨ 𝐂) ⇔ 𝐀 ∧ 𝐁 ∨ (𝐀 ∧ 𝐂).
    Proof.
      Intros [[H₁ [H₂ | H₂]] | [H₁ | H₁] [|]];
        plus [() | Apply Conjunction.introduction];
          Assumption.
    Defined.

    Theorem distributivity_with_disjunction_right 𝐀 𝐁 𝐂 :
      𝒯 ⊢ 𝐀 ∨ 𝐁 ∧ 𝐂 ⇔ 𝐀 ∧ 𝐂 ∨ (𝐁 ∧ 𝐂).
    Proof.
      Rewrite <- (Conjunction.commutativity _ 𝐂).
      Apply Conjunction.distributivity_with_disjunction_left.
    Defined.
  End Conjunction.
End Conjunction.

Module Disjunction.
  Section Disjunction.
    Context `(LogicalTheory).

    Theorem as_conditionₑ 𝐀 𝐁 𝐂 :
      𝒯 ⊢ 𝐀 ∨ 𝐁 ⇒ 𝐂 ⇔ (𝐀 ⇒ 𝐂) ∧ (𝐁 ⇒ 𝐂).
    Proof.
      Intros [H₁ [H₂ | H₂] | H₁ [H₂ | H₂]];
        Apply H₁;
        Assumption.
    Defined.

    (* C24_k *)
    Theorem distributivity_with_conjunction_left 𝐀 𝐁 𝐂 :
      𝒯 ⊢ 𝐀 ∨ (𝐁 ∧ 𝐂) ⇔ 𝐀 ∨ 𝐁 ∧ (𝐀 ∨ 𝐂).
    Proof.
      Intros [[H₁ | H₁] [|] | [[H₁ | H₁] [H₂ | H₂]]];
        plus [() | Apply Conjunction.introduction];
          Assumption.
    Defined.

    Theorem distributivity_with_conjunction_right 𝐀 𝐁 𝐂 :
      𝒯 ⊢ 𝐀 ∧ 𝐁 ∨ 𝐂 ⇔ 𝐀 ∨ 𝐂 ∧ (𝐁 ∨ 𝐂).
    Proof.
      Rewrite Disjunction.commutativity.
      Apply Disjunction.distributivity_with_conjunction_left.
    Defined.

    Theorem negationₑ 𝐀 𝐁 :
      𝒯 ⊢ ¬(𝐀 ∨ 𝐁) ⇔ ¬𝐀 ∧ ¬𝐁.
    Proof.
      unfold Conjunction.conjunction.
      Rewrite Negation.double_removal.
    Defined.
  End Disjunction.
End Disjunction.

Module Implication.
  Section Implication.
    Context `(LogicalTheory).

    Theorem negationₑ 𝐀 𝐁 :
      𝒯 ⊢ ¬(𝐀 ⇒ 𝐁) ⇔ 𝐀 ∧ ¬𝐁.
    Proof.
      Rewrite (Disjunction.negationₑ _ _ 𝐁).
      Rewrite Negation.double_removal.
    Defined.
  End Implication.
End Implication.