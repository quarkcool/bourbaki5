Require Export
  Bourbaki.Equality.Results.SingleValuedRelation.

Import Proof.TheoryHidingNotation.

Section FunctionalRelation.
  Context `{EqualitarianTheory}.

  #[export]
  Instance :
    forall {𝐑} `(!FunctionalRelation 𝒯 𝐑), SingleValuedRelation 𝒯 𝐑.
  Proof.
    Intros 𝐑 H₁ 𝒯' H₂.
    Assumption.
  Defined.

  (* C46_b *)
  Theorem from_unique_value {𝐑 y} :
    (forall x, 𝒯 ⊢ 𝐑 x ⇔ x = y) -> FunctionalRelation 𝒯 𝐑.
  Proof.
    Intros H₁ 𝒯' H₂ [|].
    { Apply H₁;
      Reflexivity. }
    { Apply SingleValuedRelation.from_single_value.
      Intros x.
      Assumption. }
  Defined.

  (* C46_a *)
  Theorem unique_value {𝐑} `(!FunctionalRelation 𝒯 𝐑) x :
    𝒯 ⊢ 𝐑 x ⇔ x = τ x, 𝐑 x.
  Proof.
    Intros [|].
    { Apply SingleValuedRelation.single_value. }
    { Intros H₁.
      Rewrite H₁.
      Assumption. }
  Defined.
End FunctionalRelation.