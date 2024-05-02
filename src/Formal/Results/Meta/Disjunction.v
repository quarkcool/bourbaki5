Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Meta.Tactic.Destruct.

Section Disjunction.
  Context `{Formal.Theory}.

  Definition destructible 𝐀 𝐁 :
    Destructible (⊢ 𝐀 ∨ 𝐁).
  Proof.
    repeat split.
  Defined.
End Disjunction.

Hint Resolve destructible | 0 : destructible_instances.