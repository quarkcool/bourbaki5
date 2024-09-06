Require Export
  Bourbaki.Logic.Results.Meta.All.

Section Disjunction.
  Context `{Logic.Truth.Theory, !Logic.Theory}.

  (* C24_ix *)
  Theorem associativity 𝐀 𝐁 𝐂 :
    ⊢ 𝐀 ∨ 𝐁 ∨ 𝐂 ⇔ (𝐀 ∨ 𝐁) ∨ 𝐂.
  Proof.
    Intros [[H₁ | [H₁ | H₁]] | [[H₁ | H₁] | H₁]];
      Assumption.
  Qed.

  (* C24_viii *)
  Theorem commutativity 𝐀 𝐁 :
    ⊢ 𝐀 ∨ 𝐁 ⇔ 𝐁 ∨ 𝐀.
  Proof.
    Intros [|];
      Apply Logic.disjunction_symmetry.
  Qed.

  Theorem operand_removal_left 𝐀 𝐁 :
    ⊢ (𝐀 ⇒ 𝐁) ⇒ (𝐀 ∨ 𝐁 ⇔ 𝐁).
  Proof.
    Intros H₁ [[| H₂] | H₂];
      Assumption.
  Qed.

  (* C24_vii *)
  Theorem idempotenceₑ 𝐀 :
    ⊢ 𝐀 ∨ 𝐀 ⇔ 𝐀.
  Proof.
    Apply Disjunction.operand_removal_left.
    Reflexivity.
  Qed.

  Theorem operand_removal_right 𝐁 𝐀 :
    ⊢ (𝐁 ⇒ 𝐀) ⇒ (𝐀 ∨ 𝐁 ⇔ 𝐀).
  Proof.
    Rewrite (Disjunction.commutativity 𝐀).
    Apply Disjunction.operand_removal_left.
  Qed.
End Disjunction.