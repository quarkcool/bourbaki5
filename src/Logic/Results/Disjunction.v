Require Export
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Logic.Results.Meta.Conjunction.

Section Disjunction.
  Context `{Logic.Theory}.

  Theorem associativity 𝐑 𝐒 𝐓 :
    ⊢ 𝐑 ∨ 𝐒 ∨ 𝐓 ⇔ 𝐑 ∨ (𝐒 ∨ 𝐓).
  Proof.
    Intros [[[H₁ | H₁] | H₁] | [H₁ | [H₁ | H₁]]];
      Assumption.
  Qed.

  (* C24_viii *)
  Theorem commutativity 𝐑 𝐒 :
    ⊢ 𝐑 ∨ 𝐒 ⇔ 𝐒 ∨ 𝐑.
  Proof.
    Intros [|];
      Apply Logic.disjunction_symmetry.
  Qed.

  Theorem operand_removal_left 𝐑 𝐒 :
    ⊢ (𝐑 ⇒ 𝐒) ⇒ (𝐑 ∨ 𝐒 ⇔ 𝐒).
  Proof.
    Intros H₁ [[H₂ | H₂] | H₂];
      plus [() | Apply H₁];
      Assumption.
  Qed.

  (* C24_vii *)
  Theorem idempotenceₑ 𝐑 :
    ⊢ 𝐑 ∨ 𝐑 ⇔ 𝐑.
  Proof.
    Apply Disjunction.operand_removal_left.
    Reflexivity.
  Qed.
End Disjunction.