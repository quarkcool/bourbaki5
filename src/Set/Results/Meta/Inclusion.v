Require Export
  Bourbaki.Equality.Results.Meta.Equality
  Bourbaki.Quantification.Results.Meta.TypicalUniversality
  Bourbaki.Set.Results.Meta.Membership
  Bourbaki.Set.Term.Subset
  Coq.Classes.Equivalence.

Module Inclusion.
  Section Inclusion.
    Context `{Equality.Theory, !Set_.Syntax}.

    Fact rewrite_lemma {T : CoercibleTerm} {x y : T} (H₁ : x ⊢⊂ y) :
      RewriteLemma H₁ (x ⊢⊂ y).
    Proof.
      split.
      Assumption.
    Defined.

    Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.

    #[export]
    Instance :
      Morphisms.Proper
        (InclusionProof --> InclusionProof ==> ImplicationProof)
        inclusion
    | 0.
    Proof.
      Intros X₂ X₁ H₁ Y₁ Y₂ H₂; unfold Basics.flip in *.
      unfold inclusion.
      Rewrite H₁.
      Rewrite H₂.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (InclusionProof ==> InclusionProof --> Basics.flip ImplicationProof)
        inclusion
    | 0 := ltac2:(flip_morphism ()).

    (* Pr_E_II_1__1 *)
    Theorem reflexivity :
      ⊢ ∀ x, x ⊂ x.
    Proof.
      Intros X x.
      Reflexivity.
    Qed.

    #[export]
    Instance :
      forall T, RelationClasses.Reflexive (InclusionProof (T := T)) | 0.
    Proof.
      Intros T x.
      Apply Inclusion.reflexivity.
    Qed.

    #[export]
    Instance :
      forall T, subrelation (EqualityProof (T := T)) InclusionProof.
    Proof.
      Intros T x y H₁.
      unfold InclusionProof.
      Rewrite H₁.
    Qed.

    #[export]
    Instance :
      forall {T : CoercibleTerm} (x : T), x ⊢⊂ x.
    Proof.
      Intros T x.
      Reflexivity.
    Qed.

    Theorem transitivity :
      ⊢ ∀ x y z, x ⊂ y ⇒ y ⊂ z ⇒ x ⊂ z.
    Proof.
      Intros X Y Z H₁ H₂ x.
      Transitivity;
        Assumption.
    Qed.

    #[export]
    Instance :
      forall T, RelationClasses.Transitive (InclusionProof (T := T)).
    Proof.
      Intros T x y z H₁ H₂.
      Apply Inclusion.transitivity;
        Assumption.
    Qed.

    Fact subset_rewrite_lemma {a x b} `(!a ⊢⊂ x) `(!b ⊢⊂ x) (H₁ : ⊢ a ⊂ b) :
      RewriteLemma H₁ ((a : Subset x) ⊢⊂ (b : Subset x)).
    Proof.
      split.
      Assumption.
    Defined.

    Fact rewrite_lemma₂ {x y} (H₁ : ⊢ x ⊂ y) :
      RewriteLemma H₁ ((x : Term) ⊢⊂ (y : Term)).
    Proof.
      split.
      Assumption.
    Defined.
  End Inclusion.

  Hint Extern 0 (RewriteLemma (T₁ := ⊢ _ ⊂ _) _ _) =>
    notypeclasses refine (subset_rewrite_lemma _ _ _) :
  rewrite_lemma_instances.

  Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.

  Hint Resolve rewrite_lemma₂ | 0 : rewrite_lemma_instances.
End Inclusion.
Export (hints) Inclusion.