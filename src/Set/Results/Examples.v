Require Export
  Bourbaki.Set.Results.CollectivizingSet.

Import Proof.TheoryHidingNotation.

Section Examples.
  Context `(EqualitarianTheory, !Set_.Syntax).

  Example C50_a
    {𝐑 𝐒} `(!CollectivizingRelation 𝒯 𝐑) `(!CollectivizingRelation 𝒯 𝐒) :
      𝒯 ⊢ (∀ x, 𝐑 x ⇒ 𝐒 x) ⇔ {x | 𝐑 x} ⊂ {x | 𝐒 x}.
  Proof.
    Rewrite CollectivizingSet.inclusionₑ.
  Defined.

  Example C50_b
    {𝐑 𝐒} `(!CollectivizingRelation 𝒯 𝐑) `(!CollectivizingRelation 𝒯 𝐒) :
      𝒯 ⊢ (∀ x, 𝐑 x ⇔ 𝐒 x) ⇔ {x | 𝐑 x} = {x | 𝐒 x}.
  Proof.
    Rewrite CollectivizingSet.equalityₑ.
  Defined.
End Examples.