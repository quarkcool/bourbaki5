Require Export
  Bourbaki.Logic.Results.All
  Bourbaki.Set.Relation.NonMembership
  Bourbaki.Set.Results.CollectivizingSet
  Bourbaki.Set.Results.Meta.Inclusion.

Module Other.
  Section Other.
    Context `{Equality.Theory, !Set_.Syntax}.

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
  End Other.
End Other.