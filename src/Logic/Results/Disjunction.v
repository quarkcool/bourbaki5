Require Export
  Bourbaki.Logic.Results.Meta.Disjunction.

Section Disjunction.
  Context `{Logic.CoreTheory}.

  Theorem excluded_middle_elimination {𝐀 𝐁} :
    ⊢ 𝐀 ⇒ 𝐁 -> ⊢ ¬𝐀 ⇒ 𝐁 -> ⊢ 𝐁.
  Proof.
    Intros H₁ H₂.
    Apply Disjunction.elimination.
    { Apply Disjunction.excluded_middle. }
    all: Assumption.
  Defined.
End Disjunction.