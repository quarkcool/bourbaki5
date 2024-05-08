Require Export
  Bourbaki.Equality.Results.Meta.Rewriting.

Import Proof.TheoryHidingNotation.

Section Equality.
  Context `(EqualitarianTheory).

  Theorem as_conditionₑ x y 𝐑 :
    𝒯 ⊢ x = y ⇒ 𝐑 x ⇔ x = y ⇒ 𝐑 y.
  Proof.
    Intros [H₁ H₂ | H₁ H₂] >
      [Rewrite <- H₂ | Rewrite H₂];
      Apply H₁;
      Assumption.
  Defined.

  (* C43 *)
  Theorem as_conjunct_leftₑ x y 𝐑 :
    𝒯 ⊢ x = y ∧ 𝐑 x ⇔ x = y ∧ 𝐑 y.
  Proof.
    Intros [H₁ [|] | H₁ [|]];
      plus [() | Apply Equality.equals_indiscernibility];
      Assumption.
  Defined.

  (* TH2 *)
  Theorem commutativity x y :
    𝒯 ⊢ x = y ⇔ y = x.
  Proof.
    Intros [|];
      Apply Equality.symmetry.
  Defined.
End Equality.