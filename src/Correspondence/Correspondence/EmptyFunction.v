Require Export
  Bourbaki.Correspondence.Correspondence.EmptyCorrespondence
  Bourbaki.Correspondence.Term.Application.

Section EmptyFunction.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall Y, IsFunction ∅ ∅ Y.
  Proof.
    Intros Y [| [x y₁ y₂ H₁ |]].
    { Exfalso.
      Apply EmptySet.emptiness;
      Assumption. }
    { Rewrite EmptyGraph.first_projectionₑ. }
  Qed.

  (* fonction vide *)
  Definition empty_function : ∅ → ∅ := ∅.
End EmptyFunction.