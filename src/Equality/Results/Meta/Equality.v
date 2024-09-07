Require Export
  Bourbaki.Equality.EqualityProof
  Bourbaki.Equality.Results.Meta.Truth
  Bourbaki.Equality.Theory
  Bourbaki.Quantification.Results.Meta.Universality.

Module Equality.
  Section Equality.
    Context `{Equality.Theory}.

    #[export]
    Instance :
      forall 𝐑 : Term -> _,
        Morphisms.Proper (EqualityProof ==> EquivalenceProof) 𝐑
    | 0.
    Proof.
      Intros 𝐑 x y H₁.
      Apply Equality.relation_rewriting.
      Assumption.
    Qed.

    #[export]
    Instance :
      forall 𝐑 : Term -> _,
        Morphisms.Proper (EqualityProof --> EquivalenceProof) 𝐑
    | 0.
    Proof.
      Intros 𝐑 y x H₁; unfold Basics.flip in *.
      Symmetry.
      Apply Equality.relation_rewriting.
      Assumption.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (pointwise_relation _ EquivalenceProof ==> EqualityProof)
        tau_abstraction
    | 0.
    Proof.
      Intros 𝐑 𝐒 H₁.
      Apply Equality.tau_abstraction_extensionality.
      Intros x.
      Assumption.
    Qed.

    Fact rewrite_lemma {T : CoercibleTerm} {x y : T} (H₁ : x ⊢= y) :
      RewriteLemma H₁ (x ⊢= y).
    Proof.
      split.
      Assumption.
    Defined.

    Fact rewrite_lemma₂ {x y} (H₁ : ⊢ x = y) :
      RewriteLemma H₁ ((x : Term) ⊢= y).
    Proof.
      split.
      Assumption.
    Defined.
  End Equality.

  Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.

  Hint Resolve rewrite_lemma₂ | 0 : rewrite_lemma_instances.

  Section Equality.
    Context `{Equality.Theory}.

    #[export]
    Instance :
      forall 𝐑 : Term -> Term -> _,
        Morphisms.Proper
          (EqualityProof ==> EqualityProof ==> EquivalenceProof)
          𝐑
    | 0.
    Proof.
      Intros 𝐑 x₁ x₂ H₁ y₁ y₂ H₂.
      Rewrite H₂.
      Apply (Equality.relation_rewriting _ _ (fun x => 𝐑 x y₂)).
      Assumption.
    Qed.
  End Equality.
End Equality.
Export (hints) Equality.