Require Export
  Bourbaki.Logic.EquivalenceProof
  Bourbaki.Logic.Results.Meta.Conjunction.

Section Equivalence.
  Context `{Logic.Theory}.

  #[export]
  Instance :
    Morphisms.Proper
      (EquivalenceProof ==> Basics.flip Basics.impl)
      Formal.Proof.
  Proof.
    Intros 𝐑 𝐒 H₁ H₂.
    Apply H₁.
    Assumption.
  Qed.

  #[export]
  Instance :
    subrelation EquivalenceProof ImplicationProof.
  Proof.
    Intros 𝐑 𝐒 H₁.
    Assumption.
  Qed.

  #[export]
  Instance :
    subrelation EquivalenceProof (Basics.flip ImplicationProof).
  Proof.
    Intros 𝐑 𝐒 H₁; unfold Basics.flip.
    Assumption.
  Qed.

  Theorem reflexivity 𝐑 :
    ⊢ 𝐑 ⇔ 𝐑.
  Proof.
    Intros [|];
      Reflexivity.
  Qed.

  #[export]
  Instance :
    Reflexive EquivalenceProof.
  Proof.
    Apply Equivalence.reflexivity.
  Qed.

  Fact rewrite_lemma {𝐑 𝐒} (H₁ : 𝐑 ⊢⇔ 𝐒) :
    RewriteLemma H₁ (𝐑 ⊢⇔ 𝐒).
  Proof.
    split.
    Assumption.
  Defined.

  (* C22_i *)
  Theorem symmetry 𝐑 𝐒 :
    ⊢ (𝐑 ⇔ 𝐒) ⇒ (𝐒 ⇔ 𝐑).
  Proof.
    Apply Conjunction.symmetry.
  Qed.

  #[export]
  Instance :
    Symmetric EquivalenceProof.
  Proof.
    Intros 𝐑 𝐒 H₁.
    Apply Equivalence.symmetry.
    Assumption.
  Qed.

  (* C22_ii *)
  Theorem transitivity 𝐑 𝐒 𝐓 :
    ⊢ (𝐑 ⇔ 𝐒) ⇒ (𝐒 ⇔ 𝐓) ⇒ (𝐑 ⇔ 𝐓).
  Proof.
    Intros H₁ H₂ [|];
      Transitivity;
        Assumption.
  Qed.

  #[export]
  Instance :
    Transitive EquivalenceProof.
  Proof.
    Intros 𝐑 𝐒 𝐓 H₁ H₂.
    Apply Equivalence.transitivity;
      Assumption.
  Qed.
End Equivalence.

Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.