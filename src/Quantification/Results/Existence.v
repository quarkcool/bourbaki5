Require Export
  Bourbaki.Logic.Results.Meta.All
  Bourbaki.Quantification.Results.Meta.Existence.

Section Existence.
  Context `{Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory}.

  Theorem removal 𝐀 :
    ⊢ (∃ _, 𝐀) ⇔ 𝐀.
  Proof.
    Rewrite Existence.definition.
  Qed.

  (* C34_ii *)
  Theorem switch 𝐑 :
    ⊢ (∃ x y, 𝐑 x y) ⇔ ∃ y x, 𝐑 x y.
  Proof.
    Intros [[x [y H₁]] | [y [x H₁]]];
      Assumption.
  Qed.
End Existence.