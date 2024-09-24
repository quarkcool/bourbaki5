Require Export
  Bourbaki.Correspondence.Correspondence.CorrespondenceComposite.

Section FunctionComposite.
  Context `{Set_.Theory}.

  (* Pr_E_II_3__6 *)
  #[export]
  Instance :
    forall {Y Z X} (g : Y → Z) (f : X → Y), IsFunction (g ∘ f) X Z.
  Proof.
    Intros Y Z X g f [| [x z₁ z₂ |]].
    { do 2 (Rewrite CoupleMembershipEquivalenceProof.proof).
      Intros [y H₁] [y' H₂].
      do 2 (Rewrite H₁).
      do 2 (Rewrite H₂). }
    { Rewrite GraphComposite.first_projectionₑ.
      Rewrite Application.first_projectionₑ.
      Rewrite Image.of_starting_set.
      Rewrite ReverseGraph.second_projectionₑ.
      Rewrite Application.first_projectionₑ. }
  Qed.

  Definition function_composite {Y Z X} (g : Y → Z) (f : X → Y) :
    X → Z :=
  g ∘ f.
End FunctionComposite.