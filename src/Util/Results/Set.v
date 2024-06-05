Require Export
  Bourbaki.Meta.Tactic.Assumption
  Bourbaki.Meta.Tactic.Intros
  Bourbaki.Meta.Tactic.Rewrite
  Bourbaki.Util.Set
  Coq.Classes.EquivDec.

Module Set_.
  Instance :
    forall T,
      CMorphisms.Proper
        (Set_.Inclusion ==> eq ==> Set_.Inclusion)
        (Set_.difference (T := T)).
  Proof.
    Intros T X U H₁ Y V H₂ x [H₃ H₄].
    rewrite <- H₂.
    split;
      plus [() | Apply H₁];
      Assumption.
  Defined.

  Instance :
    forall T,
      CMorphisms.Proper
        (Set_.Inclusion ==> Set_.Inclusion ==> Set_.Inclusion)
        (Set_.union (T := T)).
  Proof.
    Intros T X U H₁ Y V H₂ x [H₃ | H₃];
      plus [left | right];
      plus [Apply H₁ | Apply H₂];
      Assumption.
  Defined.

  Instance inclusion_reflexivity :
    forall {T} (X : Set_ T), X ⊂ X | 0.
  Proof.
    Intros T X x H₁.
    Assumption.
  Defined.

  Instance :
    forall T, CRelationClasses.Reflexive (Inclusion (T := T)).
  Proof.
    Apply @Set_.inclusion_reflexivity.
  Defined.

  Instance :
    forall T, CRelationClasses.Transitive (Inclusion (T := T)).
  Proof.
    Intros T X Y Z H₁ H₂ x H₃.
    Apply H₂.
    Apply H₁.
    Assumption.
  Defined.

  Instance :
    forall {T} {X Y : Set_ T} `(!DecidableMembership X, !DecidableMembership Y),
      DecidableMembership (X \ Y).
  Proof.
    Intros T X Y H₁ H₂ x.
    destruct (Set_.decidable_membership (X := X) x) as [H₃ | H₃].
    { destruct (Set_.decidable_membership (X := Y) x) as [H₄ | H₄].
      { right.
        Intros [_ contra₁].
        Apply contra₁.
        Assumption. }
      { left.
        split;
          Assumption. } }
    { right.
      Intros [contra₁ _].
      Apply H₃.
      Assumption. }
  Defined.

  Instance :
    forall T, DecidableMembership (T := T) ∅.
  Proof.
    Intros T x.
    right.
    Intros [].
  Defined.

  Instance :
    forall {T} `(@EqDec T eq _) (x : T), DecidableMembership {x,}.
  Proof.
    Intros T H₁ x y.
    destruct (H₁ y x) as [H₂ | H₂];
      plus [left | right];
      Assumption.
  Defined.

  Instance :
    forall {T} {X Y : Set_ T} `(!DecidableMembership X, !DecidableMembership Y),
      DecidableMembership (X ∪ Y).
  Proof.
    Intros T X Y H₁ H₂ x.
    destruct (Set_.decidable_membership (X := X) x) as [H₃ | H₃].
    { do 2 left.
      Assumption. }
    { destruct (Set_.decidable_membership (X := Y) x) as [H₄ | H₄].
      { left.
        right.
        Assumption. }
      { right.
        Intros [contra₁ | contra₁];
          plus [Apply H₃ | Apply H₄];
          Assumption. } }
  Defined.

  Instance :
    forall {T} {X : Set_ T}, ∅ ⊂ X | 0.
  Proof.
    Intros T X x H₁.
    ltac1:(exfalso).
    Assumption.
  Defined.

  Definition rewrite_lemma {T} {X Y : Set_ T} (H₁ : X ⊂ Y) :
    RewriteLemma H₁ (X ⊂ Y) :=
  {| Rewrite.rewrite_lemma := H₁ |}.

  Hint Resolve rewrite_lemma | 0 : rewrite_lemma_instances.

  Instance :
    forall {T} {X Z : Set_ T} `(X ⊂ Z) Y, X \ Y ⊂ Z | 1.
  Proof.
    Intros T X Z H₁ Y.
    Rewrite H₁.
    Intros x [H₂ _].
    Assumption.
  Defined.

  Lemma union_with_empty_set_left {T} (X : Set_ T) :
    ∅ ∪ X ⊂ X.
  Proof.
    Intros x [[] | H₁].
    Assumption.
  Defined.

  Instance :
    forall {T} {X Y : Set_ T} `(X ⊂ Y), ∅ ∪ X ⊂ Y | 1.
  Proof.
    Intros T X Y H₁.
    Rewrite Set_.union_with_empty_set_left.
  Defined.

  Instance :
    forall {T} {X U Y V : Set_ T} `(X ⊂ U) `(Y ⊂ V), X ∪ Y ⊂ U ∪ V | 1.
  Proof.
    Intros T X U Y V H₁ H₂.
    Rewrite H₁.
    Rewrite H₂.
  Defined.

  Lemma union_inclusion_left {T} (X Y : Set_ T) :
    X ⊂ X ∪ Y.
  Proof.
    Intros x H₁.
    left.
    Assumption.
  Defined.

  Instance :
    forall {T Z} `(NotEvar _ Z) {X Y : Set_ T} `(X ⊂ Y), X ⊂ Y ∪ Z | 2.
  Proof.
    Intros T Z _ X Y H₁.
    Rewrite H₁.
    Apply Set_.union_inclusion_left.
  Defined.

  Lemma union_inclusion_right {T} (Y X : Set_ T) :
    Y ⊂ X ∪ Y.
  Proof.
    Intros x H₁.
    right.
    Assumption.
  Defined.

  Instance :
    forall {T Y} `(NotEvar _ Y) {X Z : Set_ T} `(X ⊂ Z), X ⊂ Y ∪ Z | 2.
  Proof.
    Intros T Y _ X Z H₁.
    Rewrite H₁.
    Apply Set_.union_inclusion_right.
  Defined.

  Lemma difference_distributivity_with_union_right {T} (X Y Z : Set_ T) :
    X ∪ Y \ Z ⊂ X \ Z ∪ (Y \ Z).
  Proof.
    Intros x [[H₁ | H₁] H₂];
      plus [left | right];
      split;
        Assumption.
  Defined.

  Lemma difference_from_union {T} (X Y Z : Set_ T) :
    X ∪ Y \ Z ⊂ X \ Z ∪ Y.
  Proof.
    Intros x [[H₁ | H₁] H₂].
    { left.
      split;
        Assumption. }
    { right.
      Assumption. }
  Defined.

  Lemma difference_of_set_from_itself {T} (X : Set_ T) :
    X \ X ⊂ ∅.
  Proof.
    Intros x [H₁ H₂].
    ltac1:(exfalso).
    Apply H₂.
    Assumption.
  Defined.

  Lemma difference_of_operand_from_union_right {T} (X Y : Set_ T) :
    X ∪ Y \ X ⊂ Y.
  Proof.
    Rewrite Set_.difference_distributivity_with_union_right.
    Rewrite Set_.difference_of_set_from_itself.
  Defined.

  Lemma union_commutativity {T} (X Y : Set_ T) :
    X ∪ Y ⊂ Y ∪ X.
  Proof.
    Intros x [H₁ | H₁];
      plus [left | right];
      Assumption.
  Defined.

  Lemma union_with_difference_left
    {T} (X : Set_ T) {Y} `(DecidableMembership _ Y) :
      X ∪ Y ⊂ X \ Y ∪ Y.
  Proof.
    Intros x [H₁ | H₁].
    { destruct (Set_.decidable_membership x) as [H₂ | H₂].
      { right.
        Assumption. }
      { left.
        split;
          Assumption. } }
    { right.
      Assumption. }
  Defined.

  Lemma union_with_empty_set_right {T} (X : Set_ T) :
    X ∪ ∅ ⊂ X.
  Proof.
    Rewrite Set_.union_commutativity.
  Defined.
End Set_.
Export (hints) Set_.