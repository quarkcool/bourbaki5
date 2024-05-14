Require Export
  Bourbaki.Formal.Model.Meta.AxiomIndependence
  Bourbaki.Formal.Model.Results.Meta.StrongerTheoryEssence.

Section AxiomIndependence.
  Context `{𝒯 : Theory}.

  (* EX_I_2_1_a *)
  Theorem alternative_definition {𝐀} :
    CRelationClasses.iffT
      (AxiomIndependence 𝒯 𝐀)
      (𝐀 ∈ 𝒯.(ExplicitAxioms) -> 𝒯 \ {𝐀,} ⊢ 𝐀 -> False).
  Proof.
    split;
      Intros H₁ H₂ H₃;
      Apply H₁.
      { Assumption. }
      { split.
        { Intros 𝐁 H₄.
          destruct (𝐁 == 𝐀) as [H₅ | H₅].
          { rewrite H₅.
            Assumption. }
          { Apply Proof.explicit_axiom.
            split;
              Assumption. } }
        { Reflexivity. } }
      { Assumption. }
      { Rewrite H₃.
        Assumption. }
  Defined.
End AxiomIndependence.