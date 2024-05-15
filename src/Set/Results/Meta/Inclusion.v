Require Export
  Bourbaki.Quantification.Results.Meta.Universality
  Bourbaki.Set.Meta.InclusionMetaRelation.

Section Inclusion.
  Context `{QuantifiedTheory, !Equality.Syntax, !Set_.Syntax}.

  (* PROP1 *)
  Theorem reflexivity x :
    𝒯 ⊢ x ⊂ x.
  Proof.
    Intros y.
    Reflexivity.
  Defined.

  #[export]
  Instance :
    CRelationClasses.Reflexive (InclusionMetaRelation 𝒯).
  Proof.
    Apply Inclusion.reflexivity.
  Defined.

  Theorem transitivity x y z :
    𝒯 ⊢ x ⊂ y ⇒ y ⊂ z ⇒ x ⊂ z.
  Proof.
    Intros H₁ H₂ u.
    Transitivity;
      Assumption.
  Defined.

  #[export]
  Instance :
    CRelationClasses.Transitive (InclusionMetaRelation 𝒯).
  Proof.
    Intros x y z H₁ H₂.
    Apply Inclusion.transitivity;
      Assumption.
  Defined.
End Inclusion.