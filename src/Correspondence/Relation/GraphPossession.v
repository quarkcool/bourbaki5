Require Export
  Bourbaki.Correspondence.Relation.GraphEssence
  Bourbaki.Quantification.Relation.TypicalExistence.

Section GraphEssence.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  (* 𝐑 admet un graphe *)
  Definition has_graph `{Set_.Syntax} 𝐑 :=
  ∃ G ⟨is_graph⟩, ∀ x y, 𝐑 x y ⇔ ❨x, y❩ ∈ G.

  #[local] Set Typeclasses Unique Instances.
  Class HasGraph 𝐑 := graph_possession : ⊢ has_graph 𝐑.
End GraphEssence.

Hint Extern 0 (HasGraph _) => ltac:(assumption) : typeclass_instances.