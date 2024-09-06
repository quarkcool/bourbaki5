Require Export
  Bourbaki.Formal.Relation.Implication
  Bourbaki.Quantification.Relation.Universality.

Definition typical_universality `{Formal.Syntax} 𝐑 𝐒 := ∀ x, 𝐑 x ⇒ 𝐒 x.
Hint Transparent typical_universality : introduction_pattern_instances.

Notation "∀ x .. y ⟨ 𝐑 ⟩ , 𝐒" :=
  (typical_universality 𝐑 (fun x => ..
    (typical_universality 𝐑 (fun y => 𝐒)) ..)) :
bourbaki_scope.