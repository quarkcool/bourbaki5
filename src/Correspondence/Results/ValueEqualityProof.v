Require Export
  Bourbaki.Correspondence.ValueEqualityProof
  Bourbaki.Equality.Results.Meta.Equality.

Section ValueEqualityProof.
  Context `{Equality.Theory, !Set_.Syntax}.

  #[export]
  Instance :
    forall {X Y} (f : X → Y), ValueEqualityProof f (value f) | 100.
  Proof.
    Intros X Y f x.
    Reflexivity.
  Qed.
End ValueEqualityProof.