Require Export
  Bourbaki.Equality.Syntax
  Bourbaki.Logic.Results.Meta.Implication
  Bourbaki.Logic.Truth.Theory.

Section Truth.
  Context `{Logic.Theory, !Equality.Syntax}.

  #[export]
  Instance :
    Logic.Truth.Syntax :=
  {| Logic.Truth.truth := default = default ⇒ default = default |}.

  #[export]
  Instance :
    Logic.Truth.Theory.
  Proof.
    split.
    Apply Implication.reflexivity.
  Qed.
End Truth.