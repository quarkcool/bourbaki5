Require Export
  Bourbaki.Logic.Results.Conjunction
  Bourbaki.Logic.Results.Implication.

Section Equivalence.
  Context `{Logic.Truth.Theory, !Logic.Theory}.

  (* C24_iv *)
  Theorem commutativity 𝐀 𝐁 :
    ⊢ (𝐀 ⇔ 𝐁) ⇔ 𝐁 ⇔ 𝐀.
  Proof.
    Apply Conjunction.commutativity.
  Qed.

  Theorem contrapositiveₑ 𝐀 𝐁 :
    ⊢ (𝐀 ⇔ 𝐁) ⇔ ¬𝐀 ⇔ ¬𝐁.
  Proof.
    Intros [H₁ [|] | H₁ [|]].
    1-2: Apply Negation.rewriting; Assumption.
    all: Apply Implication.contrapositive; Assumption.
  Qed.
End Equivalence.