Require Export
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Logic.Results.Meta.Conjunction.

Section Implication.
  Context `{Logic.Theory}.

  (* C17 *)
  Theorem from_contrapositive 𝐁 𝐀 :
    ⊢ (¬𝐁 ⇒ ¬𝐀) ⇒ 𝐀 ⇒ 𝐁.
  Proof.
    Intros H₁ H₂ ?contra₁.
    { Apply H₂. }
    { Apply H₁.
      Assumption. }
  Defined.

  (* C24_b *)
  Theorem contrapositiveₑ 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ⇒ 𝐁 ⇔ ¬𝐁 ⇒ ¬𝐀.
  Proof.
    Intros [|].
    { Apply Negation.rewriting. }
    { Apply Implication.from_contrapositive. }
  Defined.

  (* C9 *)
  Theorem from_consequence {𝐁} 𝐀 :
    𝒯 ⊢ 𝐁 -> 𝒯 ⊢ 𝐀 ⇒ 𝐁.
  Proof.
    Intros H₁.
    Assumption.
  Defined.

  Theorem with_true_condition 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ⇒ (𝐀 ⇒ 𝐁 ⇔ 𝐁).
  Proof.
    Intros H₁ [H₂ | H₂ _];
      plus [() | Apply H₂];
      Assumption.
  Defined.
End Implication.