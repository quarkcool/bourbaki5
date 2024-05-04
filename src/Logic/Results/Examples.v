Require Export
  Bourbaki.Logic.Results.All.

Import Proof.TheoryHidingNotation.

Section Examples.
  Context `{Logic.CoreTheory}.

  Example C13 {𝐀 𝐁} 𝐂 :
    ⊢ 𝐀 ⇒ 𝐁 -> ⊢ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ⇒ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C23_b {𝐀 𝐁} 𝐂 :
    𝐀 ⊢⟨𝒯⟩⇔ 𝐁 -> 𝒯 ⊢ 𝐀 ⇒ 𝐂 ⇔ 𝐁 ⇒ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C23_c {𝐀 𝐁} 𝐂 :
    𝐀 ⊢⟨𝒯⟩⇔ 𝐁 -> 𝒯 ⊢ 𝐂 ⇒ 𝐀 ⇔ 𝐂 ⇒ 𝐁.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C23_d {𝐀 𝐁} 𝐂 :
    𝐀 ⊢⟨𝒯⟩⇔ 𝐁 -> 𝒯 ⊢ 𝐀 ∧ 𝐂 ⇔ 𝐁 ∧ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C23_e {𝐀 𝐁} 𝐂 :
    𝐀 ⊢⟨𝒯⟩⇔ 𝐁 -> 𝒯 ⊢ 𝐀 ∨ 𝐂 ⇔ 𝐁 ∨ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.

  Example C24_e 𝐀 𝐁 𝐂 :
    𝒯 ⊢ 𝐀 ∧ (𝐁 ∧ 𝐂) ⇔ 𝐀 ∧ 𝐁 ∧ 𝐂.
  Proof.
    Rewrite Conjunction.associativity.
  Defined.

  Example C24_f 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∨ 𝐁 ⇔ ¬(¬𝐀 ∧ ¬𝐁).
  Proof.
    Rewrite <- (Negation.double_removal _ (_ ∨ _)).
    Rewrite (Disjunction.negationₑ _ 𝐀).
  Defined.

  Example C24_i 𝐀 𝐁 𝐂 :
    𝒯 ⊢ 𝐀 ∨ (𝐁 ∨ 𝐂) ⇔ 𝐀 ∨ 𝐁 ∨ 𝐂.
  Proof.
    Rewrite Disjunction.associativity.
  Defined.

  Example C24_l 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∧ ¬𝐁 ⇔ ¬(𝐀 ⇒ 𝐁).
  Proof.
    Rewrite (Implication.negationₑ _ _ 𝐁).
  Defined.

  Example C24_m 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∨ 𝐁 ⇔ ¬𝐀 ⇒ 𝐁.
  Proof.
    unfold Implication.implication.
    Rewrite Negation.double_removal.
  Defined.

  Example C25_a 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 -> 𝒯 ⊢ 𝐀 ∧ 𝐁 ⇔ 𝐁.
  Proof.
    Intros H₁.
    Apply Conjunction.operand_removal_leftₑ.
    Assumption.
  Defined.

  Example C25_b 𝐀 𝐁 :
    𝒯 ⊢ ¬𝐀 -> 𝒯 ⊢ 𝐀 ∨ 𝐁 ⇔ 𝐁.
  Proof.
    Intros H₁.
    Apply Disjunction.operand_removal_leftₑ.
    Assumption.
  Defined.
End Examples.