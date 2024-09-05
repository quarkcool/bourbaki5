Require Export
  Bourbaki.Logic.Results.Meta.All.

Module Other.
  Section Other.
    Context `{Logic.Theory}.

    Lemma C13 {𝐀 𝐁} 𝐂 :
      (⊢ 𝐀 ⇒ 𝐁) -> ⊢ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ⇒ 𝐂.
    Proof.
      Intros H₁.
      Rewrite H₁.
    Qed.
  End Other.
End Other.