Require Export
  Bourbaki.Formal.ConditionalImplicationProof
  Bourbaki.Logic.ConditionalEquivalenceProof
  Bourbaki.Logic.EquivalenceProof
  Bourbaki.Logic.Results.Meta.Conjunction.

Module Equivalence.
  Section Equivalence.
    Context `{Logic.Truth.Theory, !Logic.Theory}.

    #[export]
    Instance :
      Morphisms.Proper
        (EquivalenceProof ==> Basics.flip Basics.impl)
        Formal.Proof.
    Proof.
      Intros 𝐀 𝐁 H₁ H₂.
      Apply H₁.
      Assumption.
    Qed.

    #[export]
    Instance :
      forall 𝐀,
        RelationClasses.subrelation
          (ConditionalEquivalenceProof 𝐀)
          (ConditionalImplicationProof 𝐀).
    Proof.
      Intros 𝐀 𝐁 𝐂 H₁ H₂.
      Apply H₁.
      Assumption.
    Qed.

    #[export]
    Instance :
      forall 𝐀,
        RelationClasses.subrelation
          (ConditionalEquivalenceProof 𝐀)
          (Basics.flip (ConditionalImplicationProof 𝐀)).
    Proof.
      Intros 𝐀 𝐁 𝐂 H₁ H₂.
      Apply H₁.
      Assumption.
    Qed.

    #[export]
    Instance :
      RelationClasses.subrelation EquivalenceProof ImplicationProof.
    Proof.
      Intros 𝐀 𝐁 H₁.
      Assumption.
    Qed.

    #[export]
    Instance :
      RelationClasses.subrelation
        EquivalenceProof
        (Basics.flip ImplicationProof).
    Proof.
      Intros 𝐀 𝐁 H₁; unfold Basics.flip.
      Assumption.
    Qed.

    Theorem reflexivity 𝐀 :
      ⊢ 𝐀 ⇔ 𝐀.
    Proof.
      Intros [|];
        Reflexivity.
    Qed.

    #[export]
    Instance :
      RelationClasses.Reflexive EquivalenceProof | 0.
    Proof.
      Apply Equivalence.reflexivity.
    Qed.

    (* C22_i *)
    Theorem symmetry 𝐀 𝐁 :
      ⊢ (𝐀 ⇔ 𝐁) ⇒ (𝐁 ⇔ 𝐀).
    Proof.
      Apply Conjunction.symmetry.
    Qed.

    #[export]
    Instance :
      RelationClasses.Symmetric EquivalenceProof.
    Proof.
      Intros 𝐀 𝐁 H₁.
      Apply Equivalence.symmetry.
      Assumption.
    Qed.

    #[export]
    Instance :
      forall 𝐀, RelationClasses.Symmetric (ConditionalEquivalenceProof 𝐀).
    Proof.
      Intros 𝐀 𝐁 𝐂 H₁ H₂.
      Symmetry.
      Apply H₁.
      Assumption.
    Qed.

    (* C22_ii *)
    Theorem transitivity 𝐀 𝐁 𝐂 :
      ⊢ (𝐀 ⇔ 𝐁) ⇒ (𝐁 ⇔ 𝐂) ⇒ (𝐀 ⇔ 𝐂).
    Proof.
      Intros H₁ H₂ [|];
        Transitivity;
          Assumption.
    Qed.

    #[export]
    Instance :
      RelationClasses.Transitive EquivalenceProof.
    Proof.
      Intros 𝐀 𝐁 𝐂 H₁ H₂.
      Apply Equivalence.transitivity;
        Assumption.
    Qed.

    Fact rewrite_lemma {𝐀 𝐁} (H₁ : 𝐀 ⊢⇔ 𝐁) :
      RewriteLemma H₁ (𝐀 ⊢⇔ 𝐁).
    Proof.
      split.
      Assumption.
    Defined.
  End Equivalence.

  Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.
End Equivalence.
Export (hints) Equivalence.