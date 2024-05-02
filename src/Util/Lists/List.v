Require Export
  Bourbaki.Root
  Coq.Lists.List.

Export ListNotations.

Fixpoint InT {T} x (xs : list T) : Type :=
match xs with
| [] => False
| y :: xs => (x = y) + InT x xs
end.

Theorem InT_app_or {T} {x : T} {xs₁ xs₂} :
  InT x (xs₁ ++ xs₂) -> InT x xs₁ + InT x xs₂.
Proof.
  induction xs₁ as [| y xs₁ IH₁].
  { intros H₁.
    right.
    assumption. }
  { intros [H₁ | H₁].
    { repeat left.
      assumption. }
    { destruct (IH₁ H₁) as [H₂ | H₂].
      { left.
        right.
        assumption. }
      { right.
        assumption. } } }
Defined.

Theorem InT_or_app {T} {x : T} {xs₁ xs₂} :
   InT x xs₁ + InT x xs₂ -> InT x (xs₁ ++ xs₂).
Proof.
  induction xs₁ as [| y xs₁ IH₁].
  { intros [[] | H₁].
    assumption. }
  { intros [[H₁ | H₁] | H₁].
    { left.
      assumption. }
    { right.
      apply IH₁.
      left.
      assumption. }
    { right.
      apply IH₁.
      right.
      assumption. } }
Defined.