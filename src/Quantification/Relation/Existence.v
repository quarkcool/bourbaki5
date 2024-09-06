Require Export
  Bourbaki.Formal.Syntax
  Bourbaki.Quantification.Notation.

Definition existence `{Formal.Syntax} 𝐑 := 𝐑 (τ x, 𝐑 x).

Notation "∃ x .. y , 𝐑" :=
  (existence (fun x => .. (existence (fun y => 𝐑)) ..)) :
bourbaki_scope.