Require Export
  Bourbaki.Formal.Model.ProofInBaseTheory
  Bourbaki.Formal.Model.Results.Meta.TheoryFromSet
  Bourbaki.Formal.Model.Results.Meta.TheoryUnion.

Section Model.
  Context `{𝒯 : Theory}.

  #[export]
  Instance Th :
    Formal.Theory.
  Proof.
    refine '{| Formal.Proof := ProofInBaseTheory |};
      try typeclasses_eauto.
    Intros 𝐀 𝐁 [𝐀s₁ H₁ H₂] [𝐀s₂ H₃ H₄].
    Apply {| ProofInBaseTheory.AdjoinedAxioms := 𝐀s₁ ∪ 𝐀s₂ |}.
    { Apply H₄; simpl.
      Assumption. }
  Defined.
  Canonical Th.

  #[local]
  Definition entailment_false_helper {𝐀} (H₁ : 𝒯 ⊢ 𝐀) :
    ⊢ 𝐀 :=
  Eval simpl in
  ltac2:(
    refine '{| ProofInBaseTheory.AdjoinedAxioms := ∅ |};
      try typeclasses_eauto;
    Assumption
  ).

  Definition entailment_false
    {𝐀 H₁ T} `(Entailment (x := entailment_false_helper H₁) false (⊢ 𝐀) T) :
      Entailment (x := H₁) false (𝒯 ⊢ 𝐀) T.
  Proof.
    repeat split.
    Apply _.
  Defined.

  Definition entailment_true
    {T x 𝐀} `{Entailment (x := x) true T (⊢ 𝐀)}
    `(H₁ : SolveLater (Apply.entails.(AdjoinedAxioms) ⊂ ∅)) :
      Entailment (x := x) true T (𝒯 ⊢ 𝐀).
  Proof.
    repeat split.
    Rewrite (_ : 𝒯 ⊃ ∅%mset ∪ 𝒯).
    Rewrite <- H₁.
    Apply ProofInBaseTheory.proof.
  Defined.
End Model.

Hint Resolve entailment_false | 5 : entailment_instances.

Hint Extern 1 (Entailment true _ _) =>
  simple notypeclasses refine (entailment_true _) :
entailment_instances.