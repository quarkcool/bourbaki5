Require Export
  Bourbaki.Formal.Meta.Contradiction
  Bourbaki.Logic.Results.Meta.Disjunction.

Section Negation.
  Context `{Logic.CoreTheory}.

  (* C11 *)
  Theorem double_removal 𝐀 :
    ⊢ 𝐀 ⇒ ¬¬𝐀.
  Proof.
    Apply Disjunction.excluded_middle.
  Defined.

  (* C12 *)
  Theorem rewriting 𝐀 𝐁 :
    ⊢ (𝐀 ⇒ 𝐁) ⇒ ¬𝐁 ⇒ ¬𝐀.
  Proof.
    Transitivity.
    { Apply Logic.disjunction_rewriting_right;
      Apply Negation.double_removal. }
    { Apply Logic.disjunction_commutativity. }
  Defined.

  #[export]
  Instance :
    CMorphisms.Proper
      (
        ImplicationMetaRelation ==>
          CRelationClasses.flip ImplicationMetaRelation
      )
      Formal.negation
    | 0.
  Proof.
    Intros 𝐀 𝐁 H₁; unfold CRelationClasses.flip.
    Apply Negation.rewriting.
    Assumption.
  Defined.

  #[export]
  Instance :
    CMorphisms.Proper
      (ImplicationMetaRelation --> ImplicationMetaRelation)
      Formal.negation
    | 1.
  Proof.
    assert apply_subrelation by split; typeclasses_eauto.
  Defined.

  Theorem ex_falso_quodlibet 𝐀 :
    Contradiction -> ⊢ 𝐀.
  Proof.
    Intros [𝐁 [H₁ H₂]].
    Apply (_ : ⊢ 𝐁 ⇒ 𝐀);
      Assumption.
  Defined.
End Negation.