Require Export
  Bourbaki.Formal.Model.Operation.Binding
  Bourbaki.Formal.Syntax
  Bourbaki.Meta.Tactic.Assumption
  Bourbaki.Meta.Tactic.Intros
  Bourbaki.Meta.Tactic.RelationTactics.

Section SyntaxModel.
  Context `{𝒯Syn : TheorySyntax}.

  Lemma Term_decidable_equality :
    forall x y : Syntax.Term, {x === y} + {x =/= y}

  with TermList_decidable_equality :
    forall {n} (x y : Syntax.TermList n), {x === y} + {x =/= y}

  with Relation_decidable_equality :
    forall x y : Syntax.Relation, {x === y} + {x =/= y}.
  Proof.
    { Intros [n₁ | n₁ | 𝐑₁] [n₂ | n₂ | 𝐑₂].
      all: try (right; Intros contra₁; solve [inversion contra₁]).
      { destruct (n₁ == n₂) as [H₁ | H₁].
        { left.
          rewrite H₁.
          Reflexivity. }
        { right.
          Intros contra₁.
          inversion contra₁.
          Apply H₁.
          Assumption. } }
      { destruct (n₁ == n₂) as [H₁ | H₁].
        { left.
          rewrite H₁.
          Reflexivity. }
        { right.
          Intros contra₁.
          inversion contra₁.
          Apply H₁.
          Assumption. } }
      { destruct (Relation_decidable_equality 𝐑₁ 𝐑₂) as [H₁ | H₁].
        { left.
          rewrite H₁.
          Reflexivity. }
        { right.
          Intros contra₁.
          inversion contra₁.
          Apply H₁.
          Assumption. } } }
    { Intros n₁ [| n₂ x xs] ys.
      { refine '(
          match ys with
          | nil => _
          end
        ).
        left.
        Reflexivity. }
      { refine '(
          match ys
            as ys'
            in TermList n₃
            return
              forall H₁ : n₃ = S n₂,
                {cons x xs === eq_rect _ TermList ys' _ H₁} +
                  {cons x xs =/= eq_rect _ TermList ys' _ H₁}
          with
          | nil => _
          | @cons _ n₂' y ys => _
          end eq_refl
        ).
        { Intros H₁.
          inversion H₁. }
        { Intros H₁.
          inversion H₁ as [H₂].
          revert H₁ ys.
          rewrite H₂.
          Intros H₁ ys.
          rewrite <- Eqdep_dec.eq_rect_eq_dec.
          { destruct (Term_decidable_equality x y) as [H₃ | H₃].
            { destruct (TermList_decidable_equality _ xs ys) as [H₄ | H₄].
              { left.
                rewrite H₃, H₄.
                Reflexivity. }
              { right.
                Intros contra₁.
                inversion contra₁.
                Apply H₄.
                Apply Eqdep_dec.inj_pair2_eq_dec.
                { Apply EquivDec.nat_eq_eqdec. }
                { Assumption. } } }
            { right.
              Intros contra₁.
              inversion contra₁.
              Apply H₃.
              Assumption. } }
          { Apply EquivDec.nat_eq_eqdec. } } } }
    { Intros [𝐑₁ | 𝐑₁ 𝐑₂ | sgn₁ xs₁] [𝐑₃ | 𝐑₃ 𝐑₄ | sgn₂ xs₂].
      all: try (right; Intros contra₁; solve [inversion contra₁]).
      { destruct (Relation_decidable_equality 𝐑₁ 𝐑₃) as [H₁ | H₁].
        { left.
          rewrite H₁.
          Reflexivity. }
        { right.
          Intros contra₁.
          inversion contra₁.
          Apply H₁.
          Assumption. } }
      { destruct (Relation_decidable_equality 𝐑₁ 𝐑₃) as [H₁ | H₁].
        { destruct (Relation_decidable_equality 𝐑₂ 𝐑₄) as [H₂ | H₂].
          { left.
            rewrite H₁, H₂.
            Reflexivity. }
          { right.
            Intros contra₁.
            inversion contra₁.
            Apply H₂.
            Assumption. } }
        { right.
          Intros contra₁.
          inversion contra₁.
          Apply H₁.
          Assumption. } }
      { destruct (
          𝒯Syn.(SpecificSign_decidable_equality) sgn₁ sgn₂
        ) as [H₁ | H₁].
        { revert xs₁ xs₂.
          rewrite H₁.
          Intros xs₁ xs₂.
          destruct (TermList_decidable_equality _ xs₁ xs₂) as [H₂ | H₂].
          { left.
            rewrite H₂.
            Reflexivity. }
          { right.
            Intros contra₁.
            inversion contra₁.
            Apply H₂.
            Apply (
              Eqdep_dec.inj_pair2_eq_dec
                _
                _
                (fun sgn => TermList (specific_sign_weight sgn))
            ).
            { Apply 𝒯Syn.(SpecificSign_decidable_equality). }
            { Assumption. } } }
        { right.
          Intros contra₁.
          inversion contra₁.
          Apply H₁.
          Assumption. } } }
  Defined.

  #[export]
  Instance Syn :
    Formal.Syntax :=
  {|
    Formal.Term := Syntax.Term;
    Formal.Relation := Syntax.Relation;
    Formal.Relation_decidable_equality := Relation_decidable_equality;

    Formal.tau := fun 𝐑 => Syntax.tau (bind 𝐑);

    Formal.negation := Syntax.negation;
    Formal.disjunction := Syntax.disjunction
  |}.
End SyntaxModel.
Canonical Syn.