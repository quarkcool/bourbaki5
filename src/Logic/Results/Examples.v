Require Export
  Bourbaki.Logic.Results.Meta.Proof.

Section Examples.
  Context `{Logic.CoreTheory}.

  Example C13 {𝐀 𝐁} 𝐂 :
    ⊢ 𝐀 ⇒ 𝐁 -> ⊢ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ⇒ 𝐂.
  Proof.
    Intros H₁.
    Rewrite H₁.
  Defined.
End Examples.