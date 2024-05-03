Require Export
  Bourbaki.Logic.Results.Meta.Implication.

Section Disjunction.
  Context `{Logic.CoreTheory}.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        ImplicationMetaRelation ==> ImplicationMetaRelation ==>
          ImplicationMetaRelation
      )
      Formal.disjunction
    | 0.
  Proof.
    Intros 𝐀 𝐁 H₁ 𝐂 𝐃 H₂.
    Transitivity.
    { Apply Logic.disjunction_rewriting_right.
      Assumption. }
    { Transitivity.
      { Apply Logic.disjunction_commutativity. }
      { Transitivity.
        { Apply Logic.disjunction_rewriting_right.
          Assumption. }
        { Apply Logic.disjunction_commutativity. } } }
  Defined.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        ImplicationMetaRelation --> ImplicationMetaRelation -->
          CRelationClasses.flip ImplicationMetaRelation
      )
      Formal.disjunction
    | 1.
  Proof.
    assert apply_subrelation by split; typeclasses_eauto.
  Defined.

  (* C18 *)
  Theorem elimination {𝐀 𝐁 𝐂} :
    ⊢ 𝐀 ∨ 𝐁 -> ⊢ 𝐀 ⇒ 𝐂 -> ⊢ 𝐁 ⇒ 𝐂 -> ⊢ 𝐂.
  Proof.
    Intros H₁ H₂ H₃.
    Apply Logic.disjunction_idempotence.
    Rewrite <- H₂ at 1.
    Rewrite <- H₃.
    Assumption.
  Defined.

  (* C10 *)
  Theorem excluded_middle 𝐀 :
    ⊢ 𝐀 ∨ ¬𝐀.
  Proof.
    Apply Logic.disjunction_commutativity.
    Apply Implication.reflexivity.
  Defined.

  (* C7 *)
  Theorem introduction_right 𝐁 𝐀 :
    ⊢ 𝐁 ⇒ 𝐀 ∨ 𝐁.
  Proof.
    Transitivity.
    { Apply (Logic.disjunction_introduction_left _ 𝐀). }
    { Apply Logic.disjunction_commutativity. }
  Defined.
End Disjunction.

Section Disjunction.
  Context `{Formal.Syntax}.

  Definition entailment_left
    {𝐀} `(NotEvar _ 𝐀) `{!Formal.Theory, !Logic.CoreTheory} {T x} 𝐁
    `(Entailment (x := x) true T (⊢ 𝐀)) :
      Entailment (x := x) true T (⊢ 𝐀 ∨ 𝐁).
  Proof.
    repeat split.
    Apply Logic.disjunction_introduction_left.
    Assumption.
  Defined.

  Definition entailment_right
    {𝐁} `(NotEvar _ 𝐁) `{!Formal.Theory, !Logic.CoreTheory} {T x} 𝐀
    `(Entailment (x := x) true T (⊢ 𝐁)) :
      Entailment (x := x) true T (⊢ 𝐀 ∨ 𝐁).
  Proof.
    repeat split.
    Apply Disjunction.introduction_right.
    Apply _.
  Defined.
End Disjunction.

Hint Resolve entailment_left | 2 : entailment_instances.

Hint Resolve entailment_right | 2 : entailment_instances.