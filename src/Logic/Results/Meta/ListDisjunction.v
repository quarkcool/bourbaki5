Require Export
  Bourbaki.Logic.Relation.ListDisjunction
  Bourbaki.Logic.Results.Meta.Logic.

Section ListDisjunction.
  Context `{Logic.Truth.Theory, !Logic.Theory}.

  (* Ex_E_I_3__3_ii *)
  Theorem elimination {𝐀s 𝐁} :
    Forall (fun 𝐀 => ⊢ 𝐀 ⇒ 𝐁) 𝐀s -> (⊢ list_disjunction 𝐀s) -> ⊢ 𝐁.
  Proof.
    Intros H₁ H₂.
    induction 𝐀s as [| 𝐀 𝐀s IH₁]; simpl in *.
    { Exfalso.
      Assumption. }
    { inversion H₁ as [| 𝐀' 𝐀s' H₃ H₄].
      Destruct H₂ as [| H₅].
      { Assumption. }
      { Apply IH₁;
          Assumption. } }
  Qed.
End ListDisjunction.