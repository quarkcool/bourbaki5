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

    (* Th_E_I_5__1 *)
    Theorem reflexivity :
      ⊢ ∀ x, x = x.
    Proof.
      Apply Universality.alternative_definition.
      Apply Equality.tau_abstraction_extensionality.
      Intros x.
      Reflexivity.
    Qed.

    #[export]
    Instance :
      forall T, RelationClasses.Reflexive (EqualityProof (T := T)) | 0.
    Proof.
      Intros T x.
      Apply Equality.reflexivity.
    Qed.

    (* C44 *)
    Theorem term_rewriting x y 𝐓 :
      ⊢ x = y ⇒ 𝐓 x = 𝐓 y.
    Proof.
      Intros H₁.
      Apply (Equality.relation_rewriting _ _ (fun x => 𝐓 x = 𝐓 y)).
      { Assumption. }
      { Reflexivity. }
    Qed.

    #[export]
    Instance :
      forall (𝐓 : Term -> Term),
        Morphisms.Proper (EqualityProof ==> EqualityProof) 𝐓
    | 0.
    Proof.
      Intros 𝐓 x y H₁.
      Apply (Equality.term_rewriting _ _ 𝐓).
      Assumption.
    Qed.

    (* Th_E_I_5__2 *)
    Theorem commutativity :
      ⊢ ∀ x y, x = y ⇔ y = x.
    Proof.
      Intros x y [H₁ | H₁];
        Rewrite H₁.
    Qed.

    #[export]
    Instance :
      forall T, RelationClasses.Symmetric (EqualityProof (T := T)).
    Proof.
      Intros T x y H₁.
      Apply Equality.commutativity.
      Assumption.
    Qed.

    Theorem transitivity :
      ⊢ ∀ x y z, x = y ⇒ y = z ⇒ x = z.
    Proof.
      Intros x y z H₁ H₂.
      Rewrite H₁.
      Assumption.
    Qed.

    #[export]
    Instance :
      forall T, RelationClasses.Transitive (EqualityProof (T := T)).
    Proof.
      Intros T x y z H₁ H₂.
      Apply Equality.transitivity;
        Assumption.
    Qed.

    #[export]
    Instance :
      forall (𝐓 : Term -> Term -> Term),
        Morphisms.Proper (EqualityProof ==> EqualityProof ==> EqualityProof) 𝐓
    | 0.
    Proof.
      Intros 𝐓 x₁ x₂ H₁ y₁ y₂ H₂.
      Rewrite H₂.
      Apply (Equality.term_rewriting _ _ (fun x => 𝐓 x y₂)).
      Assumption.
    Qed.
  End Equality.
End Equality.
Export (hints) Equality.