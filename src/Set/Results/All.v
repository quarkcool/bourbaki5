Require Export
  Bourbaki.Set.Relation.NonMembership
  Bourbaki.Set.Results.CollectivizingEssence.

Module Other.
  Section Other.
    Context `{Set_.Theory}.

    Lemma Pr_E_II_1__2 :
      ⊢ ∀ x y z, x ⊂ y ∧ y ⊂ z ⇒ x ⊂ z.
    Proof.
      Rewrite Conjunction.as_conditionₑ.
      Apply Inclusion.transitivity.
    Qed.

    Lemma Exa_E_II_1_4__2 :
      ⊢ ¬Coll (fun x => x ∉ x).
    Proof.
      Intros [X contra₁].
      Apply Equivalence.impossibility.
      Assumption.
    Qed.

    Lemma C50_i {𝐑 𝐒} `(!IsCollectivizing 𝐑) `(!IsCollectivizing 𝐒) :
      ⊢ (∀ x, 𝐑 x ⇒ 𝐒 x) ⇔ {x | 𝐑 x} ⊂ {x | 𝐒 x}.
    Proof.
      Rewrite CollectivizingSet.inclusionₑ.
    Qed.

    Lemma C50_ii {𝐑 𝐒} `(!IsCollectivizing 𝐑) `(!IsCollectivizing 𝐒) :
      ⊢ (∀ x, 𝐑 x ⇔ 𝐒 x) ⇔ {x | 𝐑 x} = {x | 𝐒 x}.
    Proof.
      Rewrite CollectivizingSet.equalityₑ.
    Qed.

    Lemma Rem_E_II_1__1 𝐒 {𝐑} `(!IsCollectivizing 𝐑) :
      (⊢ ∀ x, 𝐒 x ⇒ 𝐑 x) -> IsCollectivizing 𝐒.
    Proof.
      Intros H₁.
      Apply CollectivizingEssence.from_container_set.
      Intros x.
      Rewrite (MembershipEquivalenceProof.proof {x | 𝐑 x}).
      Assumption.
    Qed.
  End Other.
End Other.