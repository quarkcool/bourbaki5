Require Export
  Bourbaki.Logic.Results.Meta.Rewriting
  Bourbaki.Logic.Results.Negation.

Import Proof.TheoryHidingNotation.

Section Conjunction.
  Context `(LogicalTheory).

  Theorem as_conditionₑ 𝐀 𝐁 𝐂 :
    𝒯 ⊢ 𝐀 ∧ 𝐁 ⇒ 𝐂 ⇔ 𝐀 ⇒ 𝐁 ⇒ 𝐂.
  Proof.
    Intros [H₁ H₂ H₃ | H₁ H₂];
      Apply H₁;
        plus [() | Intros [|]];
          Assumption.
  Defined.

  Theorem as_consequenceₑ 𝐀 𝐁 𝐂 :
    𝒯 ⊢ 𝐀 ⇒ 𝐁 ∧ 𝐂 ⇔ (𝐀 ⇒ 𝐁) ∧ (𝐀 ⇒ 𝐂).
  Proof.
    Intros [H₁ [H₂ | H₂] | H₁ H₂ [|]];
      Apply H₁;
      Assumption.
  Defined.

  Theorem associativity 𝐀 𝐁 𝐂 :
    𝒯 ⊢ 𝐀 ∧ 𝐁 ∧ 𝐂 ⇔ 𝐀 ∧ (𝐁 ∧ 𝐂).
  Proof.
    Intros [H₁ [| [|]] | H₁ [[|] |]];
      Assumption.
  Defined.

  (* C24_d *)
  Theorem commutativity 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∧ 𝐁 ⇔ 𝐁 ∧ 𝐀.
  Proof.
    Intros [H₁ [|] | H₁ [|]];
      Assumption.
  Defined.

  Theorem operand_removal_rightₑ 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∧ 𝐁 ⇔ 𝐀 ⇔ 𝐀 ⇒ 𝐁.
  Proof.
    Intros [H₁ H₂ | H₁ [H₂ | H₂ [|]]];
      plus [() | Apply H₁];
      Assumption.
  Defined.

  (* C24_c *)
  Theorem idempotence 𝐀 :
    𝒯 ⊢ 𝐀 ∧ 𝐀 ⇔ 𝐀.
  Proof.
    Apply Conjunction.operand_removal_rightₑ.
    Reflexivity.
  Defined.

  Theorem negationₑ 𝐀 𝐁 :
    𝒯 ⊢ ¬(𝐀 ∧ 𝐁) ⇔ ¬𝐀 ∨ ¬𝐁.
  Proof.
    Apply Negation.double_removal.
  Defined.

  Theorem operand_removal_leftₑ 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∧ 𝐁 ⇔ 𝐁 ⇔ 𝐁 ⇒ 𝐀.
  Proof.
    Rewrite (Conjunction.commutativity 𝐀).
    Apply Conjunction.operand_removal_rightₑ.
  Defined.
End Conjunction.