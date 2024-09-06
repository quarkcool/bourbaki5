Require Export
  Bourbaki.Logic.Results.Meta.All
  Bourbaki.Quantification.Results.Meta.Existence.

Section Existence.
  Context `{Logic.Truth.Theory, !Logic.Theory}.

  Theorem removal 𝐀 :
    ⊢ (∃ _, 𝐀) ⇔ 𝐀.
  Proof.
    Rewrite Existence.definition.
  Qed.
End Existence.