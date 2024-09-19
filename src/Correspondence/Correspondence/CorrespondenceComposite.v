Require Export
  Bourbaki.Correspondence.Correspondence.ReverseCorrespondence
  Bourbaki.Correspondence.Results.GraphComposite
  Bourbaki.Correspondence.Results.Image.

Section CorrespondenceComposite.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall
      {G₁ Y Z G₂ X} `(!IsCorrespondence G₁ Y Z) `(!IsCorrespondence G₂ X Y),
        IsCorrespondence (G₁ ∘ G₂) X Z.
  Proof.
    Intros G₁ Y Z G₂ X H₁ H₂ [|].
    { Rewrite GraphComposite.first_projectionₑ.
      Rewrite Correspondence.first_projection_subset_essence.
      Rewrite Image.of_starting_set.
      Rewrite ReverseGraph.second_projectionₑ.
      Apply Correspondence.first_projection_subset_essence. }
    { Rewrite GraphComposite.second_projectionₑ.
      Rewrite Correspondence.second_projection_subset_essence.
      Rewrite Image.of_starting_set.
      Apply Correspondence.second_projection_subset_essence. }
  Qed.

  (* Def_E_II_3__7 / composée de Γ₁ et de Γ₂ *)
  Definition correspondence_composite
    {Y Z X} (Γ₁ : Correspondence Y Z) (Γ₂ : Correspondence X Y) :
      Correspondence X Z :=
  Γ₁ ∘ Γ₂.
End CorrespondenceComposite.