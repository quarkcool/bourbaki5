Require Export
  Bourbaki.Correspondence.Results.Correspondence
  Bourbaki.Correspondence.Results.ReverseGraph
  Bourbaki.Correspondence.Term.Correspondence.

Section ReverseCorrespondence.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall {G X Y} `(!IsCorrespondence G X Y), IsCorrespondence G⁻¹ Y X.
  Proof.
    Intros G X Y H₁ [|].
    { Rewrite ReverseGraph.first_projectionₑ.
      Apply Correspondence.second_projection_subset_essence. }
    { Rewrite ReverseGraph.second_projectionₑ.
      Apply Correspondence.first_projection_subset_essence. }
  Qed.

  (* correspondance réciproque de Γ *)
  Definition reverse_correspondence {X Y} (Γ : Correspondence X Y) :
    Correspondence Y X :=
  Γ⁻¹.
End ReverseCorrespondence.