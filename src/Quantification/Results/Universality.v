Require Export
  Bourbaki.Logic.Results.Negation
  Bourbaki.Quantification.Relation.Universality.

Section Universality.
  Context `{Logic.Theory}.

  (* C28 *)
  Theorem negationₑ 𝐑 :
    ⊢ ¬(∀ x, 𝐑 x) ⇔ ∃ x, ¬𝐑 x.
  Proof.
    Apply Negation.double_removalₑ.
  Qed.
End Universality.