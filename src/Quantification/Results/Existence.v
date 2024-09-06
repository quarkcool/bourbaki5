Require Export
  Bourbaki.Quantification.Results.Meta.Existence.

Section Existence.
  Context `{Quantification.Theory}.

  (* C34_ii *)
  Theorem switch 𝐑 :
    ⊢ (∃ x y, 𝐑 x y) ⇔ ∃ y x, 𝐑 x y.
  Proof.
    Intros [[x [y H₁]] | [y [x H₁]]];
      Assumption.
  Qed.
End Existence.