Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Logic.Relation.Conjunction
  Bourbaki.Meta.Tactic.Destruct.

Section Conjunction.
  Context `{Formal.Theory}.

  Definition destructible 𝐀 𝐁 :
    Destructible (⊢ 𝐀 ∧ 𝐁).
  Proof.
    repeat split.
  Defined.
End Conjunction.

Hint Resolve destructible | 0 : destructible_instances.