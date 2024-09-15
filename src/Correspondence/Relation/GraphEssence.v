Require Export
  Bourbaki.Formal.Theory
  Bourbaki.Quantification.Relation.TypicalUniversality
  Bourbaki.Set.Relation.CoupleEssence.

Section GraphEssence.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  (* Def_E_II_3__1 / G est un graphe *)
  Definition is_graph G := ∀ z ⟨∈ G⟩, is_couple z.

  #[local] Set Typeclasses Unique Instances.
  Class IsGraph G := graph_essence : ⊢ is_graph G.
End GraphEssence.

Hint Extern 0 (IsGraph _) => eassumption : typeclass_instances.

Hint Extern 0 (⊢ is_graph _) =>
  notypeclasses refine graph_essence :
typeclass_instances.