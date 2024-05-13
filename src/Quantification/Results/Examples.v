Require Export
  Bourbaki.Logic.Results.Implication
  Bourbaki.Quantification.Results.All.

Import Proof.TheoryHidingNotation.

Section Examples.
  Context `(QuantifiedTheory).

  Example C36 {𝐀 𝐑} :
    (forall x, 𝐀 x ∷ 𝒯 ⊢ 𝐑 x) -> 𝒯 ⊢ ∀ x ⟨ 𝐀 ⟩, 𝐑 x.
  Proof.
    Intros H₁ x.
    Apply Proof.deduction.
    Assumption.
  Defined.

  Example C37 {𝐑 𝐀} :
    (forall x, Contradictory (¬𝐑 x ∷ 𝐀 x ∷ 𝒯)) -> 𝒯 ⊢ ∀ x ⟨ 𝐀 ⟩, 𝐑 x.
  Proof.
    Intros H₁ x.
    destruct (H₁ x) as [𝐁 [H₂ H₃]].
    Intros H₄ ?contra₁;
      Assumption.
  Defined.

  Example EX_I_4_2 {𝐁 𝐀} :
    (forall x, 𝒯 ⊢ 𝐁 x ⇒ 𝐀) -> 𝒯 ⊢ (∃ x, 𝐁 x) ⇒ 𝐀.
  Proof.
    Intros H₁ [x H₂].
    Apply H₁.
    Assumption.
  Defined.

  Example EX_I_4_3_a 𝐀 :
    𝒯 ⊢ (∀ x y, 𝐀 x y) ⇒ ∀ x, 𝐀 x x.
  Proof.
    Intros H₁ x.
    Assumption.
  Defined.

  Example EX_I_4_3_b 𝐀 :
    𝒯 ⊢ (∃ x, 𝐀 x x) ⇒ ∃ x y, 𝐀 x y.
  Proof.
    Intros [x H₁].
    Assumption.
  Defined.

  Example EX_I_4_4_b 𝐀 𝐁 :
    𝒯 ⊢ (∃ x, 𝐀 x) ∧ (∀ x, 𝐁 x) ⇒ ∃ x, 𝐀 x ∧ 𝐁 x.
  Proof.
    Intros [[x H₁] H₂] [[|]];
      Assumption.
  Defined.

  Example EX_I_4_4_a 𝐀 𝐁 :
    𝒯 ⊢ (∀ x, 𝐀 x ∨ 𝐁 x) ⇒ (∀ x, 𝐀 x) ∨ ∃ x, 𝐁 x.
  Proof.
    Apply Implication.contrapositiveₑ.
    Rewrite Disjunction.negationₑ.
    Rewrite Universality.negationₑ.
    Rewrite Existence.negationₑ.
    Rewrite (fun _ => Disjunction.negationₑ _ (𝐀 _)).
    Apply Examples.EX_I_4_4_b.
  Defined.

  Example EX_I_4_5 `(!Inhabited Term) 𝐀 𝐁 :
    𝒯 ⊢ (∀ x y, 𝐀 x ∧ 𝐁 y) ⇔ (∀ x, 𝐀 x) ∧ ∀ y, 𝐁 y.
  Proof.
    do 2 (Rewrite Universality.split);
      Change (_ ⊢ _ ∧ (∀ _ y, _) ⇔ _).
    Rewrite Universality.removal.
  Defined.

  Example EX_I_4_6_a 𝐀 𝐑 :
    𝒯 ⊢ (∃ x ⟨ 𝐀 ⟩, 𝐑 x) ⇒ ∃ x, 𝐑 x.
  Proof.
    Intros [x H₁].
    Assumption.
  Defined.

  Example EX_I_4_6_b 𝐑 𝐀 :
    𝒯 ⊢ (∀ x, 𝐑 x) ⇒ ∀ x ⟨ 𝐀 ⟩, 𝐑 x.
  Proof.
    Intros H₁ x _.
    Assumption.
  Defined.

  Example EX_I_4_7_a {𝐑 𝐀} :
    (forall x, 𝒯 ⊢ 𝐑 x ⇒ 𝐀 x) -> 𝒯 ⊢ (∃ x, 𝐑 x) ⇔ ∃ x ⟨ 𝐀 ⟩, 𝐑 x.
  Proof.
    Intros H₁.
    unfold TypicalExistence.typical_existence.
    Rewrite (fun _ => Conjunction.operand_removal_leftₑ _ (𝐀 _)).
    Assumption.
  Defined.

  Example EX_I_4_7_b {𝐑 𝐀} :
    (forall x, 𝒯 ⊢ ¬𝐑 x ⇒ 𝐀 x) -> 𝒯 ⊢ (∀ x, 𝐑 x) ⇔ ∀ x ⟨ 𝐀 ⟩, 𝐑 x.
  Proof.
    Intros H₁.
    Rewrite <- (Negation.double_removal _ (∀ x ⟨ _ ⟩, _)).
    Rewrite TypicalUniversality.negationₑ.
    Rewrite <- Examples.EX_I_4_7_a.
    Assumption.
  Defined.

  Example EX_I_4_7_c {𝐀} 𝐑 :
    (forall x, 𝒯 ⊢ 𝐀 x) -> 𝒯 ⊢ (∃ x, 𝐑 x) ⇔ ∃ x ⟨ 𝐀 ⟩, 𝐑 x.
  Proof.
    Intros H₁.
    Apply Examples.EX_I_4_7_a.
    Intros x.
    Assumption.
  Defined.

  Example EX_I_4_7_d {𝐀} 𝐑 :
    (forall x, 𝒯 ⊢ 𝐀 x) -> 𝒯 ⊢ (∀ x, 𝐑 x) ⇔ ∀ x ⟨ 𝐀 ⟩, 𝐑 x.
  Proof.
    Intros H₁.
    Apply Examples.EX_I_4_7_b.
    Intros x.
    Assumption.
  Defined.

  Example EX_I_4_8_a {𝐀 x} 𝐑 :
    (𝒯 ⊢ 𝐀 x) -> 𝒯 ⊢ 𝐑 x ⇒ ∃ x ⟨ 𝐀 ⟩, 𝐑 x.
  Proof.
    Intros H₁ H₂ [[|]];
      Assumption.
  Defined.

  Example EX_I_4_8_b {𝐀 x} 𝐑 :
    (𝒯 ⊢ 𝐀 x) -> 𝒯 ⊢ (∀ x ⟨ 𝐀 ⟩, 𝐑 x) ⇒ 𝐑 x.
  Proof.
    Intros H₁ H₂.
    Apply H₂.
    Assumption.
  Defined.
End Examples.