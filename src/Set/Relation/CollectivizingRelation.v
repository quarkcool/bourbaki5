Require Export
  Bourbaki.Formal.Meta.StrongerTheoryEssence
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Set.Syntax.

Section CollectivizingRelation.
  Context `{Set_.Syntax}.

  Definition Coll 𝐑 := ∃ y, ∀ x, x ∈ y ⇔ 𝐑 x.
  #[export] Hint Transparent Coll : introduction_pattern_instances.

  (* relation collectivisante dans 𝒯₁ *)
  Class CollectivizingRelation 𝒯₁ 𝐑 :=
  collectivizing_essence : forall {𝒯₂} `(𝒯₂ ⟫ 𝒯₁), 𝒯₂ ⊢ Coll 𝐑.
End CollectivizingRelation.