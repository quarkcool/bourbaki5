Require Export
  Bourbaki.Equality.Results.Meta.Rewriting
  Bourbaki.Set.Relation.CollectivizingRelation
  Bourbaki.Set.Relation.Inclusion
  Bourbaki.Set.Term.CollectivizingSet.

Import Proof.TheoryHidingNotation.

Section CollectivizingSet.
  Context `{EqualitarianTheory, !Set_.Syntax}.

  Theorem membershipₑ x {𝐑} `(!CollectivizingRelation 𝒯 𝐑) :
    𝒯 ⊢ x ∈ {x | 𝐑 x} ⇔ 𝐑 x.
  Proof.
    Apply (Universality.elimination _ (fun x => x ∈ {x | 𝐑 x} ⇔ 𝐑 x)).
    Assumption.
  Defined.

  Theorem equalityₑ
    {𝐑 𝐒} `(!CollectivizingRelation 𝒯 𝐑) `(!CollectivizingRelation 𝒯 𝐒) :
      𝒯 ⊢ {x | 𝐑 x} = {x | 𝐒 x} ⇔ ∀ x, 𝐑 x ⇔ 𝐒 x.
  Proof.
    Intros [H₁ x | H₁].
    { Rewrite <- CollectivizingSet.membershipₑ.
      Rewrite H₁. }
    { unfold CollectivizingSet.collectivizing_set.
      Rewrite H₁. }
  Defined.

  Theorem inclusionₑ
    {𝐑 𝐒} `(!CollectivizingRelation 𝒯 𝐑) `(!CollectivizingRelation 𝒯 𝐒) :
      𝒯 ⊢ {x | 𝐑 x} ⊂ {x | 𝐒 x} ⇔ ∀ x, 𝐑 x ⇒ 𝐒 x.
  Proof.
    Rewrite <- CollectivizingSet.membershipₑ at 4 5.
  Defined.
End CollectivizingSet.