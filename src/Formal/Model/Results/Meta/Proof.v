Require Export
  Bourbaki.Formal.Model.Proof
  Bourbaki.Meta.Tactic.Apply
  Bourbaki.Meta.Tactic.Rewrite.

Section Proof.
  Context `{𝒯 : Theory}.

  Definition explicit_axiom_entailment
    {𝐀 H₁ T} `(Entailment (x := Proof.explicit_axiom H₁) false (𝒯 ⊢ 𝐀) T) :
      Entailment (x := H₁) false (𝐀 ∈ 𝒯.(ExplicitAxioms)) T.
  Proof.
    repeat split.
    Apply _.
  Defined.

  Definition schema_entailment
    {𝐀 H₁ T} `(Entailment (x := Proof.implicit_axiom H₁) false (𝒯 ⊢ 𝐀) T) :
      Entailment (x := H₁) false (𝐀 ∈ 𝒯.(Schemas)) T.
  Proof.
    repeat split.
    Apply _.
  Defined.

  Definition schema_rewrite_lemma
    {𝐀} {H₁ : 𝐀 ∈ 𝒯.(Schemas)} {T}
    `(RewriteLemma _ (Proof.implicit_axiom H₁) T) :
      RewriteLemma H₁ T :=
  {| Rewrite.rewrite_lemma := Rewrite.rewrite_lemma |}.

  Definition theory_hiding 𝐀 :
    GoalHiding (𝒯 ⊢ 𝐀) :=
  {|
    Util.HiddenGoal := Util.unbox (Util.box 𝒯) ⊢ 𝐀;
    Util.goal_hiding := fun H₁ => H₁
  |}.
End Proof.

Hint Resolve explicit_axiom_entailment | 2 : entailment_instances.

Hint Resolve schema_entailment | 2 : entailment_instances.

Hint Resolve schema_rewrite_lemma | 2 : rewrite_lemma_instances.

Hint Resolve theory_hiding | 0 : goal_hiding_instances.