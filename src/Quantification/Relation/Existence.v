Require Export
  Bourbaki.Formal.Syntax
  Bourbaki.Quantification.Notation.

Module Type Existence_Locked.
  Parameter body : forall `{Formal.Syntax}, (Term -> Relation) -> Relation.

  Parameter unlock : forall `{Formal.Syntax} 𝐑, body 𝐑 = 𝐑 (τ x, 𝐑 x).
End Existence_Locked.

Module Existence : Existence_Locked.
  Definition body `{Formal.Syntax} 𝐑 := 𝐑 (τ x, 𝐑 x).

  Definition unlock `{Formal.Syntax} 𝐑 : body 𝐑 = 𝐑 (τ x, 𝐑 x) := eq_refl.
End Existence.

Notation existence := Existence.body.

Notation "∃ x .. y , 𝐑" :=
  (existence (fun x => .. (existence (fun y => 𝐑)) ..)) :
bourbaki_scope.