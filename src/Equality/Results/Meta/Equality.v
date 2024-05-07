Require Export
  Bourbaki.Equality.Meta.EqualityMetaRelation
  Bourbaki.Equality.Theory
  Bourbaki.Logic.Results.Meta.Equivalence
  Bourbaki.Quantification.Results.Meta.Universality.

Section Equality.
  Context `{Equality.Syntax}.

  Definition rewrite_lemma {𝒯 x y} (H₁ : x ⊢⟨𝒯⟩= y) :
    RewriteLemma H₁ (x ⊢⟨𝒯⟩= y) :=
  {| Rewrite.rewrite_lemma := H₁ |}.
End Equality.

Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.

Section Equality.
  Context `(EqualitarianTheory).

  (* TH1 *)
  Theorem reflexivity x :
    𝒯 ⊢ x = x.
  Proof.
    Apply (Universality.elimination _ (fun x => x = x)).
    Apply Universality.alternative_definition.
    Apply Equality.tau_rewriting.
    Intros y.
    Reflexivity.
  Defined.

  #[export]
  Instance :
    CRelationClasses.Reflexive (EqualityMetaRelation 𝒯).
  Proof.
    Apply Equality.reflexivity.
  Defined.
End Equality.

Section Equality.
  Context `(EqualitarianTheory).

  Theorem symmetry x y :
    𝒯 ⊢ x = y ⇒ y = x.
  Proof.
    Intros H₁.
    Apply Equality.equals_indiscernibility.
    { Assumption. }
    { Reflexivity. }
  Defined.

  #[export]
  Instance :
    CRelationClasses.Symmetric (EqualityMetaRelation 𝒯).
  Proof.
    Intros x y H₁.
    Apply Equality.symmetry.
    Assumption.
  Defined.
End Equality.

Section Equality.
  Context `(EqualitarianTheory).

  Theorem transitivity x y z :
    𝒯 ⊢ x = y ⇒ y = z ⇒ x = z.
  Proof.
    Intros H₁ H₂.
    Apply (Equality.equals_indiscernibility _ _ (fun x => x = z));
      Assumption.
  Defined.

  #[export]
  Instance :
    CRelationClasses.Transitive (EqualityMetaRelation 𝒯).
  Proof.
    Intros x y z H₁ H₂.
    Apply Equality.transitivity;
      Assumption.
  Defined.
End Equality.