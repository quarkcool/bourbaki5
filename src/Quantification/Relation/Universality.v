Require Export
  Bourbaki.Quantification.Relation.Existence.

Definition universality `{Formal.Syntax} 𝐑 := ¬∃ x, ¬𝐑 x.

Notation "∀ x .. y , 𝐑" :=
  (universality (fun x => .. (universality (fun y => 𝐑)) ..)) :
bourbaki_scope.