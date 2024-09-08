Require Export
  Bourbaki.Equality.Relation.UnequivocalEssence
  Bourbaki.Quantification.Results.All
  Bourbaki.Set.Results.Meta.Inclusion
  Bourbaki.Set.Theory.

Module Set_.
  Section Set_.
    Context `{Set_.Theory}.

    Theorem equalityₑ₂ :
      ⊢ ∀ x y, x = y ⇔ x ⊂ y ∧ y ⊂ x.
    Proof.
      Intros x y [H₁ [|] |].
      1-2: Rewrite H₁.
      { Apply Conjunction.as_conditionₑ.
        Apply Set_.extensionality. }
    Qed.

    Theorem equalityₑ :
      ⊢ ∀ X Y, X = Y ⇔ ∀ x, x ∈ X ⇔ x ∈ Y.
    Proof.
      Intros X Y.
      Rewrite Set_.equalityₑ₂.
      Rewrite <- Universality.split.
    Qed.

    (* C48 *)
    #[export]
    Instance :
      forall 𝐑, IsUnequivocal (fun X => ∀ x, x ∈ X ⇔ 𝐑 x).
    Proof.
      Intros 𝐑 X₁ X₂ H₁ H₂.
      Apply Set_.equalityₑ.
      Intros x.
      Rewrite H₁.
      Rewrite H₂.
    Qed.
  End Set_.
End Set_.
Export (hints) Set_.