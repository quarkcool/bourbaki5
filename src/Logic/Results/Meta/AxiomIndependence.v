Require Export
  Bourbaki.Formal.Meta.AxiomIndependence
  Bourbaki.Logic.Results.Meta.Proof
  Bourbaki.Logic.Results.Meta.TailTheory
  Bourbaki.Truth.Results.Theory.

Section AxiomIndependence.
  Context `(TruthTheory, !LogicalTheory 𝒯).

  (* EX_I_3_5 *)
  Theorem alternative_definition₂ :
    let 𝒯' := ¬List.hd ⊤ 𝒯.(explicit_axioms) ∷ TailTheory 𝒯 in
    CRelationClasses.iffT (AxiomIndependence 𝒯) (Contradictory 𝒯' -> False).
  Proof.
    destruct 𝒯 as [[| 𝐀 𝐀s] Sc]; simpl.
    { split.
      { Intros H₁ _.
        Apply H₁. }
      { Intros H₁ _.
        Apply H₁.
        do 2 esplit.
        { Apply Truth.truth_truth. }
        { Apply Proof.explicit_axiom.
          left.
          Reflexivity. } } }
    { split.
      { Intros H₁ [𝐁 [H₂ H₃]].
        Apply H₁.
        split.
        { Intros 𝐂 [H₄ | H₄].
          { rewrite H₄.
            Intros ?contra₁;
              Assumption. }
          { Apply Proof.explicit_axiom.
            Assumption. } }
        { Intros 𝐂.
          Apply id. } }
      { Intros H₁ H₂.
        Apply H₁.
        do 2 esplit.
        { Rewrite H₂.
          Apply Proof.explicit_axiom.
          right.
          left.
          Reflexivity. }
        { Apply Proof.explicit_axiom.
          left.
          Reflexivity. } } }
  Defined.
End AxiomIndependence.