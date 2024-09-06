Require Export
  Bourbaki.Quantification.Results.Existence
  Bourbaki.Quantification.Results.Meta.Universality.

Section Universality.
  Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

  (* C28 *)
  Theorem negationₑ 𝐑 :
    ⊢ ¬(∀ x, 𝐑 x) ⇔ ∃ x, ¬𝐑 x.
  Proof.
    Apply Negation.double_removalₑ.
  Qed.

  Theorem removal 𝐀 :
    ⊢ (∀ _, 𝐀) ⇔ 𝐀.
  Proof.
    unfold universality.
    Rewrite Existence.removal.
    Apply Negation.double_removalₑ.
  Qed.

  (* C34_i *)
  Theorem switch 𝐑 :
    ⊢ (∀ x y, 𝐑 x y) ⇔ ∀ y x, 𝐑 x y.
  Proof.
    Intros [H₁ y x | H₁ x y];
      Assumption.
  Qed.
End Universality.