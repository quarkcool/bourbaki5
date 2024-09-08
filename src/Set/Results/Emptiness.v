Require Export
  Bourbaki.Set.Results.Complement.

Section Emptiness.
  Context `{Set_.Theory}.

  (* Th_E_II_1__1 *)
  #[export]
  Instance functional_essence :
    IsFunctional is_empty.
  Proof.
    Intros [| X₁ X₂ H₁ H₂].
    { Apply Complement.of_set_relative_to_itself_emptiness.
      Apply Util.default. }
    { Apply Set_.equalityₑ.
      Intros x [H₃ | H₃];
        Exfalso;
        plus [Apply H₁ | Apply H₂];
        Assumption. }
  Qed.
End Emptiness.