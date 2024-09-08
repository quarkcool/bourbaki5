Require Export
  Bourbaki.Equality.Results.Meta.Equality
  Bourbaki.Meta.Tactic.Change
  Bourbaki.Quantification.Results.Meta.TypicalUniversality
  Bourbaki.Set.MembershipEquivalenceProof
  Bourbaki.Set.Relation.CollectivizingEssence
  Bourbaki.Set.Relation.Inclusion
  Bourbaki.Set.Term.CollectivizingSet.

Section CollectivizingSet.
  Context `{Equality.Theory, !Set_.Syntax}.

  #[export]
  Instance :
    forall {𝐑} `(!IsCollectivizing 𝐑),
      MembershipEquivalenceProof {x | 𝐑 x} 𝐑.
  Proof.
    Intros 𝐑; unfold IsCollectivizing.
    Rewrite Existence.definition.
    Apply id.
  Qed.

  Theorem equalityₑ {𝐑 𝐒} `(!IsCollectivizing 𝐑) `(!IsCollectivizing 𝐒) :
    ⊢ {x | 𝐑 x} = {x | 𝐒 x} ⇔ ∀ x, 𝐑 x ⇔ 𝐒 x.
  Proof.
    Intros [H₁ x | H₁].
    { Rewrite <- MembershipEquivalenceProof.proof.
      Rewrite H₁. }
    { Change (⊢ (τ X, _) = τ X, _).
      Rewrite H₁. }
  Qed.

  Theorem inclusionₑ {𝐑 𝐒} `(!IsCollectivizing 𝐑) `(!IsCollectivizing 𝐒) :
    ⊢ {x | 𝐑 x} ⊂ {x | 𝐒 x} ⇔ ∀ x ⟨𝐑⟩, 𝐒 x.
  Proof.
    unfold inclusion.
    Rewrite MembershipEquivalenceProof.proof.
  Qed.
End CollectivizingSet.