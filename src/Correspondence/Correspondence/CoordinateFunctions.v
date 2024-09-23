Require Export
  Bourbaki.Correspondence.Correspondence.TermFunction
  Bourbaki.Correspondence.Results.GraphProjections.

Section CoordinateFunctions.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall G : Graph, set_by_replacement pr₁ G ⊢⊂ pr₁⟨G⟩.
  Proof.
    Intros G;
      Change (⊢ _ ⊂ _).
    Rewrite GraphProjections.alternative_definition₁.
  Qed.

  #[export]
  Instance :
    forall G : Graph, set_by_replacement pr₂ G ⊢⊂ pr₂⟨G⟩.
  Proof.
    Intros G;
      Change (⊢ _ ⊂ _).
    Rewrite GraphProjections.alternative_definition₂.
  Qed.

  (* première fonction coordonnée sur G *)
  Definition coordinate_function₁ (G : Graph) := z ∈ G ↦ pr₁ z ∈ pr₁⟨G⟩.

  (* seconde fonction coordonnée sur G *)
  Definition coordinate_function₂ (G : Graph) := z ∈ G ↦ pr₂ z ∈ pr₂⟨G⟩.
End CoordinateFunctions.