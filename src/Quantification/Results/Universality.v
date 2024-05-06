Require Export
  Bourbaki.Quantification.Results.Meta.Universality.

Import Proof.TheoryHidingNotation.

Section Universality.
  Context `(QuantifiedTheory).

  (* C28 *)
  Theorem negationₑ 𝐑 :
    𝒯 ⊢ ¬(∀ x, 𝐑 x) ⇔ ∃ x, ¬𝐑 x.
  Proof.
    Apply Negation.double_removal.
  Defined.

  Theorem removal `(!Inhabited Term) 𝐀 :
    𝒯 ⊢ (∀ _, 𝐀) ⇔ 𝐀.
  Proof.
    Intros [H₁ | H₁ _];
      Apply H₁.
      { Apply Util.default. }
  Defined.

  (* C34_a *)
  Theorem switch 𝐑 :
    𝒯 ⊢ (∀ x y, 𝐑 x y) ⇔ ∀ y x, 𝐑 x y.
  Proof.
    Intros [H₁ y x | H₁ x y];
      Assumption.
  Defined.
End Universality.