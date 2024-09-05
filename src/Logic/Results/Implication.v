Require Export
  Bourbaki.Logic.Results.Meta.Disjunction.

Section Implication.
  Context `{Logic.Theory}.

  (* C9 *)
  Theorem from_consequence {𝐒} 𝐑 :
    (⊢ 𝐒) -> ⊢ 𝐑 ⇒ 𝐒.
  Proof.
    Intros H₁.
    Assumption.
  Qed.
End Implication.