Require Export
  Bourbaki.Logic.Results.Negation
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Quantification.Results.Meta.Existence.

Section Universality.
  Context `(QuantifiedTheory).

  (* C26 *)
  Theorem alternative_definition 𝐑 :
    𝒯 ⊢ (∀ x, 𝐑 x) ⇔ 𝐑 (τ x, ¬𝐑 x).
  Proof.
    Apply Negation.double_removal.
  Defined.

  (* C30 *)
  Theorem elimination 𝐑 x :
    𝒯 ⊢ (∀ x, 𝐑 x) ⇒ 𝐑 x.
  Proof.
    Intros H₁ ?contra₁.
    2: Apply H₁.
    Assumption.
  Defined.

  Definition entailment
    {𝐑 : Term -> _} {H₁} {x : SolveLater _} {𝐀}
    `(
      Entailment
        (x := Proof.syllogism H₁ (Universality.elimination _ _))
        false
        (𝒯 ⊢ 𝐑 x)
        (𝒯 ⊢ 𝐀)
    ) :
      Entailment (x := H₁) false (𝒯 ⊢ Universality.universality 𝐑) (𝒯 ⊢ 𝐀).
  Proof.
    split.
    { Apply _. }
    { split. }
  Defined.

  (* C27 *)
  Theorem introduction 𝐑 :
    (forall x, 𝒯 ⊢ 𝐑 x) -> 𝒯 ⊢ ∀ x, 𝐑 x.
  Proof.
    Intros H₁.
    Apply Universality.alternative_definition.
    Assumption.
  Defined.

  Definition introduction_pattern 𝐑 :
    IntroductionPattern simple_pattern (𝒯 ⊢ Universality.universality 𝐑) :=
  {| Intros.introduction_pattern := Universality.introduction _ |}.

  Definition rewrite_lemma
    {𝐑} {H₁ : 𝒯 ⊢ ∀ x, 𝐑 x} {TT}
    `(
      lem :
        forall x,
          RewriteLemma
            (Proof.syllogism H₁ (Universality.elimination _ x))
            (TT x)
    ) :
      RewriteLemma H₁ (forall x, TT x) :=
  {| Rewrite.rewrite_lemma := fun x => Rewrite.rewrite_lemma |}.
End Universality.

Hint Resolve entailment | 3 : entailment_instances.

Hint Resolve introduction_pattern | 0 : introduction_pattern_instances.

Hint Resolve rewrite_lemma | 2 : rewrite_lemma_instances.