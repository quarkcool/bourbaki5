Require Export
  Bourbaki.Correspondence.Results.EmptyGraph
  Bourbaki.Correspondence.Term.Correspondence.

Section EmptyCorrespondence.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall X Y, IsCorrespondence ∅ X Y.
  Proof.
    Intros X Y [|].
    { Rewrite EmptyGraph.first_projectionₑ.
      Apply EmptySet.subset_essence. }
    { Rewrite EmptyGraph.second_projectionₑ.
      Apply EmptySet.subset_essence. }
  Qed.

  Definition empty_correspondence : Correspondence ∅ ∅ := ∅.
End EmptyCorrespondence.