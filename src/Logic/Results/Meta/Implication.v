Require Export
  Bourbaki.Formal.Results.Meta.Proof
  Bourbaki.Logic.CoreTheory
  Coq.Setoids.Setoid.

Section Implication.
  Context `{Logic.CoreTheory}.

  #[export]
  Instance :
    forall 𝐀,
      CMorphisms.Proper
        (ImplicationMetaRelation ==> ImplicationMetaRelation)
        (Implication.implication 𝐀)
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
        (Implication.implication 𝐀)
      | 1.
  Proof.
    assert apply_subrelation by split; typeclasses_eauto.
  Defined.

  (* C6 *)
  Theorem transitivity {𝐀 𝐁 𝐂} :
    ⊢ 𝐀 ⇒ 𝐁 -> ⊢ 𝐁 ⇒ 𝐂 -> ⊢ 𝐀 ⇒ 𝐂.
  Proof.
    Intros H₁ H₂.
    Rewrite <- H₂.
    Assumption.
  Defined.

  #[export]
  Instance :
    CRelationClasses.Transitive ImplicationMetaRelation.
  Proof.
    Apply @Implication.transitivity.
  Defined.

  (* C8 *)
  Theorem reflexivity 𝐀 :
    ⊢ 𝐀 ⇒ 𝐀.
  Proof.
    Transitivity.
    { Apply (Logic.disjunction_introduction_left _ 𝐀). }
    { Apply Logic.disjunction_idempotence. }
  Defined.

  #[export]
  Instance :
    CRelationClasses.Reflexive ImplicationMetaRelation.
  Proof.
    Apply Implication.reflexivity.
  Defined.
End Implication.