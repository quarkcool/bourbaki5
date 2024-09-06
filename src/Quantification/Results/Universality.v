Require Export
  Bourbaki.Logic.Results.Negation
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Quantification.Results.Existence.

Section Universality.
  Context `{Logic.Truth.Theory, !Logic.Theory}.

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
End Universality.