Require Export
  Bourbaki.Formal.Results.Meta.Implication
  Bourbaki.Logic.CoreTheory
  Bourbaki.Meta.Tactic.Assumption
  Bourbaki.Meta.Tactic.Intros.

Section Disjunction.
  Context `{Logic.CoreTheory}.

  #[export]
  Instance :
    forall 𝐀,
      CMorphisms.Proper
        (ImplicationMetaRelation ==> ImplicationMetaRelation)
        (Formal.disjunction 𝐀)
      | 0.
  Proof.
    Intros 𝐀 𝐁 𝐂 H₁.
    Apply Logic.disjunction_rewriting_right.
    Assumption.
  Defined.

  #[export]
  Instance :
    forall 𝐀,
      CMorphisms.Proper
        (
          ImplicationMetaRelation -->
            CRelationClasses.flip ImplicationMetaRelation
        )
        (Formal.disjunction 𝐀)
      | 1.
  Proof.
    assert apply_subrelation by split; typeclasses_eauto.
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
End Disjunction.

Hint Resolve entailment_left | 1 : entailment_instances.