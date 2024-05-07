Require Export
  Bourbaki.Equality.Relation.Inequality
  Bourbaki.Equality.Results.Meta.Equality.

Section Theory.
  Context `{EqualitarianTheory}.

  #[export]
  Instance :
    Falsity.Syntax :=
  {| Falsity.falsity := (τ x, x = x) ≠ (τ x, x = x) |}.

  #[export]
  Instance :
    FalsityTheory 𝒯.
  Proof.
    split.
    { Intros 𝐀 [H₁ | []].
      rewrite H₁.
      Apply Negation.double_removal.
      Reflexivity. }
    { Intros 𝐀 []. }
  Defined.
End Theory.