Require Export
  Bourbaki.Formal.Results.Meta.Disjunction
  Bourbaki.Logic.Relation.ListDisjunction
  Bourbaki.Logic.Results.Disjunction
  Bourbaki.Logic.Results.Meta.Rewriting.

Section ListDisjunction.
  Context `(FalsityTheory, !LogicalTheory 𝒯).

  (* EX_I_3_3_b *)
  Theorem elimination {𝐀s 𝐁} :
    𝒯 ⊢ list_disjunction 𝐀s -> (forall 𝐀, InT 𝐀 𝐀s -> 𝒯 ⊢ 𝐀 ⇒ 𝐁) ->
      𝒯 ⊢ 𝐁.
  Proof.
    enough (
      H₁ :
        forall 𝒯' `(𝒯' ⟫ 𝒯),
          𝒯' ⊢ list_disjunction 𝐀s ->
          (forall 𝐀, InT 𝐀 𝐀s -> 𝒯' ⊢ 𝐀 ⇒ 𝐁) ->
            𝒯' ⊢ 𝐁
    ).
    { Apply H₁. }
    { induction 𝐀s as [| 𝐀 𝐀s IH₁].
      { simpl; Intros 𝒯' H₁ H₂ _.
        Apply Negation.ex_falso_quodlibet.
        do 2 esplit.
        { Assumption. }
        { Apply Falsity.falsity_impossibility. } }
      { simpl; Intros 𝒯' H₁ H₂ H₃.
        Destruct H₂ as [H₄ | H₄].
        { Apply H₃.
          { left.
            Reflexivity. }
          { Assumption. } }
        { Apply IH₁.
          { Assumption. }
          { Intros 𝐂 H₅.
            Apply H₃.
            right.
            Assumption. } } } }
  Defined.

  Let IntroTheoryHelper 𝒯 𝐀s :=
  List.fold_right (fun 𝐀 𝒯 => 𝐀 ∷ 𝒯) 𝒯 (List.map Formal.negation 𝐀s).

  #[export]
  Instance :
    forall {𝐀 𝒯 𝐀s},
      IntroTheoryHelper (𝐀 ∷ 𝒯) 𝐀s ⟫ 𝐀 ∷ IntroTheoryHelper 𝒯 𝐀s.
  Proof.
    induction 𝐀s as [| 𝐁 𝐀s IH₁].
    { Reflexivity. }
    { unfold IntroTheoryHelper in *; simpl.
      Rewrite IH₁.
      Apply TheoryAdjunction.switch. }
  Defined.

  (* EX_I_3_3_a *)
  Theorem introduction {𝐀s 𝐀} :
    IntroTheoryHelper 𝒯 𝐀s ⊢ 𝐀 -> 𝒯 ⊢ list_disjunction (𝐀 :: 𝐀s).
  Proof.
    enough (
      H₁ :
        forall 𝒯' `(𝒯' ⟫ 𝒯),
          IntroTheoryHelper 𝒯' 𝐀s ⊢ 𝐀 -> 𝒯' ⊢ list_disjunction (𝐀 :: 𝐀s)
    ).
    { Apply H₁. }
    { induction 𝐀s as [| 𝐁 𝐀s IH₁].
      { simpl; Intros 𝒯' H₁ H₂.
        Assumption. }
      { simpl; Intros 𝒯' H₁ H₂.
        Destruct (Disjunction.excluded_middle _ 𝐁) as [H₃ | H₃].
        { Assumption. }
        { Rewrite <- Disjunction.associativity.
          Rewrite (Disjunction.commutativity _ 𝐀).
          Rewrite Disjunction.associativity.
          Apply IH₁.
          Assumption. } } }
  Defined.
End ListDisjunction.