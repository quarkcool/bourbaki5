Require Export
  Bourbaki.Equality.Relation.Inequality
  Bourbaki.Set.Relation.NonEmptiness
  Bourbaki.Set.Results.CollectivizingEssence
  Bourbaki.Set.Results.CoupleCoordinates
  Bourbaki.Set.Results.EmptySet
  Bourbaki.Set.Results.Product
  Bourbaki.Set.Term.Product.

Module Complement.
  Section Complement.
    Context `{Set_.Theory}.

    Theorem of_empty_set :
      ⊢ ∀ x, ∁ x ∅ = x.
    Proof.
      Rewrite Set_.equalityₑ.
      Intros X x.
      Rewrite MembershipEquivalenceProof.proof.
      Apply Conjunction.operand_removal_left.
      Apply EmptySet.emptiness.
    Qed.

    Theorem of_set_relative_to_itself :
      ⊢ ∀ x, ∁ x x = ∅.
    Proof.
      Rewrite EmptySet.as_equalₑ.
      Apply Complement.of_set_relative_to_itself_emptiness.
    Qed.
  End Complement.
End Complement.

Module Couple.
  Section Couple.
    Context `{Set_.Theory}.

    Theorem as_equalₑ :
      ⊢ ∀ z x y, z = ❨x, y❩ ⇔ is_couple z ∧ x = pr₁ z ∧ y = pr₂ z.
    Proof.
      Intros z x y.
      do 2 (Rewrite <- Existence.conjunct_extraction_right);
        Change (⊢ _ ⇔ ∃ x' y', _).
      Rewrite (
        fun _ _ =>
          Equality.as_conjunct_leftₑ _ _ (fun z => _ = pr₁ z ∧ y = pr₂ z)
      ).
      Rewrite CoupleCoordinates.of_couple₁.
      Rewrite CoupleCoordinates.of_couple₂.
      Rewrite Equality.commutativity at 3 4.
      Rewrite (fun _ _ => Conjunction.commutativity (_ = _)).
      Rewrite <- Conjunction.associativity.
      Rewrite Existence.conjunct_extraction_left;
        Change (⊢ _ ⇔ ∃ x', _ ∧ ∃ y', _).
      do 2 (Rewrite Existence.of_equalₑ).
    Qed.
  End Couple.
End Couple.

Module CoupleEssence.
  Section CoupleEssence.
    Context `{Set_.Theory}.

    Theorem alternative_definition :
      ⊢ ∀ x, is_couple x ⇔ x = ❨pr₁ x, pr₂ x❩.
    Proof.
      Intros z [[x [y H₁]] | H₁ [[]]].
      { Rewrite H₁.
        Rewrite CoupleCoordinates.of_couple₁.
        Rewrite CoupleCoordinates.of_couple₂. }
      { Assumption. }
    Qed.
  End CoupleEssence.
End CoupleEssence.

Module Existence.
  Section Existence.
    Context `{Set_.Theory}.

    Theorem of_equal_coupleₑ 𝐑 :
      ⊢ ∀ z, (∃ x y, z = ❨x, y❩ ∧ 𝐑 x y) ⇔ is_couple z ∧ 𝐑 (pr₁ z) (pr₂ z).
    Proof.
      Intros z.
      Rewrite Couple.as_equalₑ.
      do 2 (Rewrite <- Conjunction.associativity).
      do 3 (Rewrite Existence.conjunct_extraction_left);
        Change (⊢ _ ∧ (∃ x, _ ∧ ∃ y, _) ⇔ _).
      do 2 (Rewrite Existence.of_equalₑ).
    Qed.

    Theorem of_equal_coupleₑ₂ 𝐑 :
      ⊢ ∀ x y, (∃ x' y', ❨x, y❩ = ❨x', y'❩ ∧ 𝐑 x' y') ⇔ 𝐑 x y.
    Proof.
      Intros x y.
      Rewrite Existence.of_equal_coupleₑ.
      Rewrite CoupleCoordinates.of_couple₁.
      Rewrite CoupleCoordinates.of_couple₂.
      Rewrite (Conjunction.operand_removal_left _ (is_couple _)).
      Apply Couple.couple_essence.
    Qed.
  End Existence.
End Existence.

Module NonEmptiness.
  Section NonEmptiness.
    Context `{Set_.Theory}.

    Theorem alternative_definition :
      ⊢ ∀ x, is_non_empty x ⇔ ¬is_empty x.
    Proof.
      Intros X.
      Rewrite Universality.negationₑ.
      Rewrite Negation.double_removalₑ.
    Qed.

    Theorem alternative_definition₂ :
      ⊢ ∀ x, is_non_empty x ⇔ x ≠ ∅.
    Proof.
      Intros x.
      unfold inequality.
      Rewrite EmptySet.as_equalₑ.
      Apply NonEmptiness.alternative_definition.
    Qed.
  End NonEmptiness.
End NonEmptiness.

Module Product.
  Section Product.
    Context `{Set_.Theory}.

    Theorem emptinessₑ :
      ⊢ ∀ X Y, is_empty (X × Y) ⇔ is_empty X ∨ is_empty Y.
    Proof.
      Intros X Y.
      Apply Equivalence.contrapositiveₑ.
      Rewrite (Disjunction.negationₑ (is_empty _)).
      Rewrite <- NonEmptiness.alternative_definition.
      Change (⊢ (∃ z, _) ⇔ _).
      Rewrite MembershipEquivalenceProof.proof.
      Intros [[z [x [y H₁]]] [|] | [[x H₁] [y H₂]] [[[[| [|]]]]]];
        first [Assumption | Reflexivity].
    Qed.

    (* Pr_E_II_2__2 *)
    Theorem inclusionₑ :
      ⊢ ∀ X₁ Y₁ ⟨is_non_empty⟩, ∀ X₂ Y₂, X₁ × Y₁ ⊂ X₂ × Y₂ ⇔ X₁ ⊂ X₂ ∧ Y₁ ⊂ Y₂.
    Proof.
      Intros X₁ [x' H₁] Y₁ [y' H₂] X₂ Y₂.
      Change (⊢ (∀ z, _) ⇔ _).
      Rewrite MembershipEquivalenceProof.proof.
      Rewrite Existence.of_equal_coupleₑ.
      Intros [H₃ [x H₄ | y H₄] | H₃ z H₄ [| [|]]].
      1-2:
        plus [
          Rewrite <- (⇑(⇑CoupleCoordinates.of_couple₁ _) y') at 1
        |
          Rewrite <- (⇑CoupleCoordinates.of_couple₂ x') at 1
        ];
        Apply H₃;
        Intros [| [|]].
      1,4: Apply Couple.couple_essence.
      1,3: Rewrite CoupleCoordinates.of_couple₁; Assumption.
      1-2: Rewrite CoupleCoordinates.of_couple₂; Assumption.
      { Assumption. }
      all:
        Apply H₃;
        Assumption.
    Qed.
  End Product.
End Product.

Module Singleton.
  Section Singleton.
    Context `{Set_.Theory}.

    (* Ex_E_II_1__4 *)
    Theorem as_supersetₑ {X x} :
      ⊢ X ⊂ {x,} ⇔ X = {x,} ∨ X = ∅.
    Proof.
      Rewrite Set_.equalityₑ₂ at 1.
      Rewrite Singleton.as_subsetₑ.
      Rewrite Disjunction.distributivity_over_conjunction_right.
      Rewrite (Disjunction.operand_removal_right _ (_ ⊂ _)).
      { Rewrite (Conjunction.operand_removal_right (_ ⊂ _)).
        Rewrite (Disjunction.commutativity (_ ∈ _)).
        Rewrite <- (Negation.as_conditionₑ (_ = _)).
        Rewrite <- NonEmptiness.alternative_definition₂.
        Intros H₁ [y H₂].
        Rewrite <- (_ : y ⊢= x).
        { Apply (MembershipEquivalenceProof.proof _ (fun y => y = x)).
          Apply H₁.
          Assumption. }
        { Assumption. } }
      { Intros H₁.
        Rewrite H₁.
        Apply EmptySet.subset_essence. }
    Qed.
  End Singleton.
End Singleton.

Module TypicalExistence.
  Section TypicalExistence.
    Context `{Set_.Theory}.

    Theorem of_coupleₑ 𝐑 :
      ⊢ (∃ z ⟨is_couple⟩, 𝐑 (pr₁ z) (pr₂ z)) ⇔ ∃ x y, 𝐑 x y.
    Proof.
      unfold typical_existence;
        Change (⊢ (∃ z, _) ⇔ _).
      Rewrite <- Existence.of_equal_coupleₑ.
      Rewrite Existence.switch at 1; Rewrite Existence.switch at 2;
        Change (⊢ (∃ x y z, _) ⇔ _).
      Rewrite Existence.conjunct_extraction_right;
        Change (⊢ (∃ x y, (∃ z, _) ∧ _) ⇔ _).
      Rewrite (fun _ _ => Conjunction.operand_removal_left (𝐑 _ _)).
      Apply Equality.reflexivity.
    Qed.
  End TypicalExistence.
End TypicalExistence.

Module Universality.
  Section Universality.
    Context `{Set_.Theory}.

    Theorem over_equal_couplesₑ 𝐑 :
      ⊢ ∀ z, (∀ x y, z = ❨x, y❩ ⇒ 𝐑 x y) ⇔ is_couple z ⇒ 𝐑 (pr₁ z) (pr₂ z).
    Proof.
      Intros z.
      Rewrite Couple.as_equalₑ.
      do 2 (Rewrite Conjunction.as_conditionₑ).
      Rewrite Universality.condition_extraction;
        Change (⊢ (∀ x, _ ⇒ ∀ y, _) ⇔ _).
      do 2 (Rewrite TypicalUniversality.over_equalsₑ).
    Qed.
  End Universality.
End Universality.

Module TypicalUniversality.
  Section TypicalUniversality.
    Context `{Set_.Theory}.

    Theorem over_couplesₑ 𝐑 :
      ⊢ (∀ z ⟨is_couple⟩, 𝐑 (pr₁ z) (pr₂ z)) ⇔ ∀ x y, 𝐑 x y.
    Proof.
      Change (⊢ (∀ z, _) ⇔ _).
      Rewrite <- Universality.over_equal_couplesₑ.
      Rewrite Universality.switch at 1; Rewrite Universality.switch at 2;
        Change (⊢ (∀ x y z, _) ⇔ _).
      Rewrite Universality.consequence_extraction;
        Change (⊢ (∀ x y, (∃ z, _) ⇒ _) ⇔ _).
      Rewrite Implication.with_true_condition.
      Apply Equality.reflexivity.
    Qed.
  End TypicalUniversality.
End TypicalUniversality.

Module Other.
  Section Other.
    Context `{Set_.Theory}.

    Lemma Pr_E_II_1__2 :
      ⊢ ∀ x y z, x ⊂ y ∧ y ⊂ z ⇒ x ⊂ z.
    Proof.
      Rewrite Conjunction.as_conditionₑ.
      Apply Inclusion.transitivity.
    Qed.

    Lemma Exa_E_II_1_4__2 :
      ⊢ ¬Coll (fun x => x ∉ x).
    Proof.
      Intros [X contra₁].
      Apply Equivalence.impossibility.
      Assumption.
    Qed.

    Lemma C50_i {𝐑 𝐒} `(!IsCollectivizing 𝐑) `(!IsCollectivizing 𝐒) :
      ⊢ (∀ x, 𝐑 x ⇒ 𝐒 x) ⇔ {x | 𝐑 x} ⊂ {x | 𝐒 x}.
    Proof.
      Rewrite CollectivizingSet.inclusionₑ.
    Qed.

    Lemma C50_ii {𝐑 𝐒} `(!IsCollectivizing 𝐑) `(!IsCollectivizing 𝐒) :
      ⊢ (∀ x, 𝐑 x ⇔ 𝐒 x) ⇔ {x | 𝐑 x} = {x | 𝐒 x}.
    Proof.
      Rewrite CollectivizingSet.equalityₑ.
    Qed.

    Lemma Rem_E_II_1__1 𝐒 {𝐑} `(!IsCollectivizing 𝐑) :
      (⊢ ∀ x, 𝐒 x ⇒ 𝐑 x) -> IsCollectivizing 𝐒.
    Proof.
      Intros H₁.
      Apply CollectivizingEssence.from_container_set.
      Intros x.
      Rewrite (MembershipEquivalenceProof.proof {x | 𝐑 x}).
      Assumption.
    Qed.

    Lemma Rem_E_II_1__2 :
      ⊢ ¬∃ X, ∀ x, x ∈ X.
    Proof.
      Intros [X contra₁].
      Apply Other.Exa_E_II_1_4__2.
      Apply CollectivizingEssence.from_container_set.
      Intros x _.
      Assumption.
    Qed.

    Lemma Ex_E_II_1__1 x y :
      ⊢ x = y ⇔ ∀ X, x ∈ X ⇒ y ∈ X.
    Proof.
      Intros [H₁ X | H₁].
      { Rewrite H₁. }
      { Symmetry.
        Apply (MembershipEquivalenceProof.proof _ (fun y => y = x)).
        Apply H₁.
        Apply MembershipEquivalenceProof.proof.
        Reflexivity. }
    Qed.

    Lemma Ex_E_II_1__2_i x :
      ⊢ ∅ ≠ {x,}.
    Proof.
      Intros contra₁.
      Apply EmptySet.emptiness; Change (⊢ _ ∈ _).
      Rewrite contra₁.
      Apply MembershipEquivalenceProof.proof.
      Reflexivity.
    Qed.

    Lemma Ex_E_II_1__2_ii :
      ⊢ ∃ x y, x ≠ y.
    Proof.
      Apply Other.Ex_E_II_1__2_i.
      Apply Util.default.
    Qed.

    Lemma Ex_E_II_1__5 :
      ⊢ ∅ = τ X, (τ x, x ∈ X) ∉ X.
    Proof.
      unfold empty_set;
        Change (⊢ (τ X, _) = _).
      Rewrite Universality.alternative_definition.
      Rewrite Negation.double_removalₑ.
    Qed.

    Lemma Pr_E_II_2__3 :
      ⊢ ∀ A B, A × B = ∅ ⇔ A = ∅ ∨ B = ∅.
    Proof.
      Rewrite EmptySet.as_equalₑ.
      Apply Product.emptinessₑ.
    Qed.

    Lemma Ex_E_II_2__1_i 𝐑 :
      ⊢ (∃ x y, 𝐑 x y) ⇔ ∃ z, is_couple z ∧ 𝐑 (pr₁ z) (pr₂ z).
    Proof.
      Rewrite TypicalExistence.of_coupleₑ.
    Qed.

    Lemma Ex_E_II_2__1_ii 𝐑 :
      ⊢ (∀ x y, 𝐑 x y) ⇔ ∀ z, is_couple z ⇒ 𝐑 (pr₁ z) (pr₂ z).
    Proof.
      Rewrite TypicalUniversality.over_couplesₑ.
    Qed.
  End Other.

  Section Ex_E_II_1__6.
    Context `{Equality.Theory, !Set_.Syntax}.
    Context (A1' : ⊢ ∀ y, y = τ x, ∀ z, z ∈ x ⇔ z ∈ y).

    Lemma Ex_E_II_1__6 :
      ⊢ ∀ x y, x ⊂ y ⇒ y ⊂ x ⇒ x = y.
    Proof.
      Intros X Y H₁ H₂.
      Rewrite A1'.
      Rewrite (_ : ⊢ ∀ z, z ∈ X ⇔ z ∈ Y).
      Apply Universality.split.
      Intros [|];
        Assumption.
    Qed.
  End Ex_E_II_1__6.
End Other.