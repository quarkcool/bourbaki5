Require Export
  Bourbaki.Equality.Relation.SingleValuedRelation
  Bourbaki.Equality.Results.Meta.Rewriting.

Import Proof.TheoryHidingNotation.

Section SingleValuedRelation.
  Context `{EqualitarianTheory}.

  (* C45_b *)
  Theorem from_single_value {𝐑 y} :
    (forall x, 𝒯 ⊢ 𝐑 x ⇒ x = y) -> SingleValuedRelation 𝒯 𝐑.
  Proof.
    Intros H₁ 𝒯' H₂ u H₃ v H₄.
    Rewrite H₁;
      Assumption.
  Defined.

  (* C45_a *)
  Theorem single_value {𝐑} `(!SingleValuedRelation 𝒯 𝐑) x :
    𝒯 ⊢ 𝐑 x ⇒ x = τ x, 𝐑 x.
  Proof.
    Intros H₁.
    Apply SingleValuedRelation.single_valued_essence.
    { Assumption. }
    { Change (_ ⊢ ∃ x, 𝐑 x).
      Assumption. }
  Defined.
End SingleValuedRelation.