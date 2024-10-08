Require Export
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Logic.Results.Meta.Conjunction.

Section Negation.
  Context `{Logic.Truth.Theory, !Logic.Theory}.

  (* C24_i *)
  Theorem double_removalₑ 𝐀 :
    ⊢ ¬¬𝐀 ⇔ 𝐀.
  Proof.
    Intros [|].
    { Apply Negation.doubling. }
    { Apply Negation.double_removal. }
  Qed.
End Negation.