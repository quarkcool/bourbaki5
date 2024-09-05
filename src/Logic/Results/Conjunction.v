Require Export
  Bourbaki.Logic.Relation.Conjunction
  Bourbaki.Logic.Results.Meta.Negation.

Section Conjunction.
  Context `{Logic.Theory}.

  Theorem impossibility 𝐀 :
    ⊢ ¬(𝐀 ∧ ¬𝐀).
  Proof.
    Apply Negation.double_removal.
    Rewrite <- Negation.double_removal.
    Apply Implication.reflexivity.
  Qed.
End Conjunction.