Require Export
  Bourbaki.Set.Results.Pair
  Bourbaki.Set.Term.Singleton.

Section Singleton.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall x, MembershipEquivalenceProof {x,} (= x) | 0.
  Proof.
    Intros x y.
    Rewrite MembershipEquivalenceProof.proof.
    Apply Disjunction.idempotenceₑ.
  Qed.

  Theorem typical_universalityₑ 𝐑 :
    ⊢ ∀ x, (∀ y ⟨∈ {x,}⟩, 𝐑 y) ⇔ 𝐑 x.
  Proof.
    Intros x.
    Rewrite Pair.typical_universalityₑ.
    Apply Conjunction.idempotenceₑ.
  Qed.

  Theorem as_subsetₑ :
    ⊢ ∀ x X, {x,} ⊂ X ⇔ x ∈ X.
  Proof.
    Intros x X.
    Apply Singleton.typical_universalityₑ.
  Qed.

  Theorem equality_to_pair_leftₑ :
    ⊢ ∀ x y z, {x, y} = {z,} ⇔ x = z ∧ y = z.
  Proof.
    Intros x y z.
    Rewrite Pair.equalityₑ.
    Apply Disjunction.idempotenceₑ.
  Qed.

  Theorem equalityₑ :
    ⊢ ∀ x y, {x,} = {y,} ⇔ x = y.
  Proof.
    Intros x y.
    Rewrite Singleton.equality_to_pair_leftₑ.
    Apply Conjunction.idempotenceₑ.
  Qed.

  Theorem equality_to_pair_rightₑ :
    ⊢ ∀ x y z, {x,} = {y, z} ⇔ x = y ∧ x = z.
  Proof.
    Intros x y z.
    Rewrite Equality.commutativity.
    Apply Singleton.equality_to_pair_leftₑ.
  Qed.

  Theorem typical_existenceₑ 𝐑 :
    ⊢ ∀ x, (∃ y ⟨∈ {x,}⟩, 𝐑 y) ⇔ 𝐑 x.
  Proof.
    Intros x.
    Rewrite Pair.typical_existenceₑ.
    Apply Disjunction.idempotenceₑ.
  Qed.
End Singleton.