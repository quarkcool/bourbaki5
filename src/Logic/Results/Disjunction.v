Require Export
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Logic.Results.Meta.Conjunction.

Section Disjunction.
  Context `{Logic.CoreTheory}.

  Theorem associativity 𝐀 𝐁 𝐂 :
    𝒯 ⊢ 𝐀 ∨ 𝐁 ∨ 𝐂 ⇔ 𝐀 ∨ (𝐁 ∨ 𝐂).
  Proof.
    Intros [[[H₁ | H₁] | H₁] | [H₁ | [H₁ | H₁]]];
      Assumption.
  Defined.

  (* C24_h *)
  Theorem commutativity 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∨ 𝐁 ⇔ 𝐁 ∨ 𝐀.
  Proof.
    Intros [|];
      Apply Logic.disjunction_commutativity.
  Defined.

  Theorem excluded_middle_elimination {𝐀 𝐁} :
    ⊢ 𝐀 ⇒ 𝐁 -> ⊢ ¬𝐀 ⇒ 𝐁 -> ⊢ 𝐁.
  Proof.
    Intros H₁ H₂.
    Apply Disjunction.elimination.
    { Apply Disjunction.excluded_middle. }
    all: Assumption.
  Defined.

  Theorem operand_removal_leftₑ 𝐀 𝐁 :
    𝒯 ⊢ 𝐀 ∨ 𝐁 ⇔ 𝐁 ⇔ 𝐀 ⇒ 𝐁.
  Proof.
    Intros [H₁ H₂ | H₁ [[H₂ | H₂] | H₂]];
      plus [() | Apply H₁];
      Assumption.
  Defined.

  (* C24_g *)
  Theorem idempotence 𝐀 :
    𝒯 ⊢ 𝐀 ∨ 𝐀 ⇔ 𝐀.
  Proof.
    Apply Disjunction.operand_removal_leftₑ.
    Reflexivity.
  Defined.
End Disjunction.