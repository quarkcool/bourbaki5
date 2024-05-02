Require Export
  Bourbaki.Formal.Meta.Contradiction
  Bourbaki.Logic.Results.Meta.Disjunction.

Section Negation.
  Context `{Logic.CoreTheory}.

  Theorem ex_falso_quodlibet 𝐀 :
    Contradiction -> ⊢ 𝐀.
  Proof.
    Intros [𝐁 [H₁ H₂]].
    Apply (_ : ⊢ 𝐁 ⇒ 𝐀);
      Assumption.
  Defined.
End Negation.