Require Export
  Bourbaki.Formal.Meta.ConditionalMetaRelation
  Bourbaki.Logic.Meta.EquivalenceMetaRelation
  Bourbaki.Logic.Results.Meta.Conjunction.

Section Equivalence.
  Context `(LogicalTheory).

  Theorem reflexivity 𝐀 :
    𝒯 ⊢ 𝐀 ⇔ 𝐀.
  Proof.
    Intros [|];
      Reflexivity.
  Defined.

  #[export]
  Instance :
    CRelationClasses.Reflexive (EquivalenceMetaRelation 𝒯).
  Proof.
    Apply Equivalence.reflexivity.
  Defined.

  (* C22_a *)
  Theorem symmetry {𝐀 𝐁} :
    𝒯 ⊢ 𝐀 ⇔ 𝐁 -> 𝒯 ⊢ 𝐁 ⇔ 𝐀.
  Proof.
    Apply Conjunction.symmetry.
  Defined.

  #[export]
  Instance :
    CRelationClasses.Symmetric (EquivalenceMetaRelation 𝒯).
  Proof.
    Apply @Equivalence.symmetry.
  Defined.

  (* C22_b *)
  Theorem transitivity {𝐀 𝐁 𝐂} :
    𝒯 ⊢ 𝐀 ⇔ 𝐁 -> 𝒯 ⊢ 𝐁 ⇔ 𝐂 -> 𝒯 ⊢ 𝐀 ⇔ 𝐂.
  Proof.
    Intros H₁ H₂ [|];
      Transitivity;
        Assumption.
  Defined.

  #[export]
  Instance :
    CRelationClasses.Transitive (EquivalenceMetaRelation 𝒯).
  Proof.
    Apply @Equivalence.transitivity.
  Defined.

  Definition rewrite_lemma {𝒯 𝐀 𝐁} (H₁ : 𝐀 ⊢⟨𝒯⟩⇔ 𝐁) :
    RewriteLemma H₁ (𝐀 ⊢⟨𝒯⟩⇔ 𝐁) :=
  {| Rewrite.rewrite_lemma := H₁ |}.

  Definition theory_hiding x y :
    GoalHiding (x ⊢⟨𝒯⟩⇔ y) :=
  {|
    Util.HiddenGoal := x ⊢⟨Util.unbox (Util.box 𝒯)⟩⇔ y;
    Util.goal_hiding := fun H₁ => H₁
  |}.
End Equivalence.

Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.

Hint Resolve theory_hiding | 0 : goal_hiding_instances.

Section Equivalence.
  Context `(LogicalTheory).

  #[export]
  Instance :
    forall 𝐀,
      CRelationClasses.Symmetric
        (ConditionalMetaRelation 𝒯 𝐀 Equivalence.equivalence).
  Proof.
    Intros 𝐀 𝐁 𝐂 H₁ H₂.
    Symmetry.
    Apply H₁.
    Assumption.
  Defined.
End Equivalence.