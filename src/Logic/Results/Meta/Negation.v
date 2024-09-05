Require Export
  Bourbaki.Logic.Results.Meta.Logic.

Module Negation.
  Section Negation.
    Context `{Logic.Theory, !Logic.Truth.Syntax}.

    Fact entailment {𝐀} {H₁ : SolveLater (⊢ 𝐀)} {H₂ : ⊢ ¬𝐀} :
      Entailment false H₂ (⊢ ⊥).
    Proof.
      repeat split.
      Apply Logic.ex_falso_quodlibet.
      repeat esplit;
        Assumption.
    Defined.
  End Negation.

  Hint Resolve entailment | 1 : entailment_instances.
End Negation.
Export (hints) Negation.