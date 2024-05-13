Require Export
  Bourbaki.Formal.Meta.TailTheory
  Bourbaki.Logic.Theory
  Bourbaki.Meta.Tactic.Apply
  Bourbaki.Meta.Tactic.Intros.

Section TailTheory.
  Context `(LogicalTheory).

  #[export]
  Instance :
    LogicalTheory (TailTheory 𝒯).
  Proof.
    split.
    { Intros 𝐀 []. }
    { simpl.
      Apply StrongerTheoryEssence.weaker_schema. }
  Defined.
End TailTheory.