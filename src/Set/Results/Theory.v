Require Export
  Bourbaki.Meta.Tactic.Apply
  Bourbaki.Meta.Tactic.RelationTactics
  Bourbaki.Set.Theory.

Import Proof.TheoryHidingNotation.

Module Set_.
  Section Set_.
    Context `(SetTheory).

    (* axiome d'extensionalité *)
    Theorem extensionality :
      𝒯 ⊢ ∀ x y, x ⊂ y ⇒ y ⊂ x ⇒ x = y.
    Proof.
      Apply StrongerTheoryEssence.weaker_explicit_axiom.
      left.
      Reflexivity.
    Defined.
  End Set_.
End Set_.