Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Set.Syntax.

Section CollectivizingEssence.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  Definition Coll 𝐑 := ∃ X, ∀ x, x ∈ X ⇔ 𝐑 x.

  #[local] Set Typeclasses Unique Instances.
  (* 𝐑 est collectivisante en x *)
  Class IsCollectivizing 𝐑 := collectivizing_essence : ⊢ Coll 𝐑.
End CollectivizingEssence.