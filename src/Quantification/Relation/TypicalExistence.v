Require Export
  Bourbaki.Logic.Relation.Conjunction
  Bourbaki.Quantification.Relation.Existence.

Definition typical_existence `{Formal.Syntax} 𝐑 𝐒 := ∃ x, 𝐑 x ∧ 𝐒 x.

Notation "∃ x .. y ⟨ 𝐑 ⟩ , 𝐒" :=
  (typical_existence 𝐑 (fun x => .. (typical_existence 𝐑 (fun y => 𝐒)) ..)) :
bourbaki_scope.