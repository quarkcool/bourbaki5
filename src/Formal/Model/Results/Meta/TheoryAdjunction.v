Require Export
  Bourbaki.Formal.Model.Meta.StrongerTheoryEssence
  Bourbaki.Formal.Model.Meta.TheoryAdjunction
  Bourbaki.Formal.Model.Results.Meta.Proof
  Bourbaki.Util.Results.Set.

Section TheoryAdjunction.
  Context `{𝒯 : Theory}.

  (*
  #[export]
  Instance :
    CMorphisms.Proper
      (StrongerTheoryEssence ==> Logic.eq ==> StrongerTheoryEssence)
      TheoryAdjunction
    | 0.
  Proof.
    Intros 𝒯₂ 𝒯₁ H₁ 𝐀 𝐁 H₂.
    rewrite H₂.
    split.
    { Intros 𝐂 [H₃ | H₃].
      { rewrite H₃.
        Apply Proof.explicit_axiom.
        left.
        Reflexivity. }
      { Assumption. } }
    { Intros 𝐂.
      Apply StrongerTheoryEssence.weaker_schema. }
  Defined.

  #[export]
  Instance :
    forall 𝒯,
      CMorphisms.Proper
        (ImplicationMetaRelation ==> StrongerTheoryEssence)
        (TheoryAdjunction 𝒯)
      | 0.
  Proof.
    Intros 𝒯 𝐀 𝐁 H₁.
    split.
    { Intros 𝐂 [H₂ | H₂].
      { rewrite H₂.
        Apply H₁.
        Apply Proof.explicit_axiom.
        left.
        Reflexivity. }
      { Assumption. } }
    { Intros 𝐂.
      Apply id. }
  Defined.

  Definition switch 𝐀 𝐁 𝒯 :
    𝐀 ∷ 𝐁 ∷ 𝒯 ⟫ 𝐁 ∷ 𝐀 ∷ 𝒯.
  Proof.
    split.
    { Intros 𝐂 [H₁ | [H₁ | H₁]].
      { rewrite H₁.
        Apply Proof.explicit_axiom.
        right.
        left.
        Reflexivity. }
      { rewrite H₁.
        Apply Proof.explicit_axiom.
        left.
        Reflexivity. }
      { Apply Proof.explicit_axiom.
        right.
        right.
        Assumption. } }
    { Intros 𝐂.
      Apply id. }
  Defined.

  #[export]
  Instance :
    forall {𝐀 𝒯₂ 𝒯₁} `(𝐀 ∷ 𝒯₂ ⟫ 𝒯₁) 𝐁, 𝐀 ∷ 𝐁 ∷ 𝒯₂ ⟫ 𝒯₁ | 4.
  Proof.
    Intros 𝐀 𝒯₂ 𝒯₁ H₁ 𝐁.
    Transitivity.
    { Apply TheoryAdjunction.switch. }
    { typeclasses_eauto. }
  Defined.*)

  Definition absorption {𝐀} :
    𝒯 ⊢ 𝐀 -> 𝒯 ⊃ 𝐀 ∷ 𝒯.
  Proof.
    Intros H₁.
    split.
    { Intros 𝐁 [H₂ | H₂].
      { rewrite H₂.
        Assumption. }
      { Assumption. } }
    { typeclasses_eauto. }
  Defined.
End TheoryAdjunction.