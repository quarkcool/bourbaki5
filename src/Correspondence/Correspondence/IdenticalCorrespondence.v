Require Export
  Bourbaki.Correspondence.Results.Diagonal
  Bourbaki.Correspondence.Term.Correspondence.

Section IdenticalCorrespondence.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall X, IsCorrespondence (Δ X) X X.
  Proof.
    Intros X [|].
    { Rewrite Diagonal.first_projectionₑ. }
    { Rewrite Diagonal.second_projectionₑ. }
  Qed.

  (* correspondance identique de X *)
  Definition identical_correspondence X : Correspondence X X := Δ X.
End IdenticalCorrespondence.

Notation Id := identical_correspondence.