Require Export
  Bourbaki.Equality.Results.Meta.Equality
  Bourbaki.Meta.Tactic.Change
  Bourbaki.Set.Term.CollectivizingSet.

Module CollectivizingSet.
  Section CollectivizingSet.
    Context `{Equality.Theory, !Set_.Syntax}.

    #[export]
    Instance :
      Morphisms.Proper
        (pointwise_relation _ EquivalenceProof ==> EqualityProof)
        collectivizing_set
    | 1.
    Proof.
      Intros 𝐑 𝐒 H₁.
      Change ((τ X, ∀ x, x ∈ X ⇔ 𝐑 x) ⊢= _).
      Rewrite H₁.
    Qed.
  End CollectivizingSet.
End CollectivizingSet.
Export (hints) CollectivizingSet.