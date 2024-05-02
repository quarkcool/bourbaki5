Require Export
  Bourbaki.Meta.Tactic.RelationTactics
  Coq.Classes.Morphisms.

Create HintDb rewrite_lemma_instances discriminated.

Class RewriteLemma {T₁} (x : T₁) T₂ := { rewrite_lemma : T₂ }.

Ltac2 rewrite_impl ori cstr_with_bindings_th occs id :=
Util.on_hidden_goal (
  fun () =>
    let cstr_th :=
      fun () => let (cstr, _) := cstr_with_bindings_th () in cstr
    in
    refine '(let __rewrite_lemma := Rewrite.rewrite_lemma in _) > [|
      Control.refine cstr_th
    | |
      ltac1:(
        unshelve (
          typeclasses eauto with rewrite_lemma_instances typeclass_instances
        )
      )
    |];
    Control.enter (
      fun () =>
        lazy_match! goal with
        | [h := rewrite_lemma |- _] =>
          let cstr := Util.hyp_unfold h in
          clear __rewrite_lemma;
          Std.setoid_rewrite
            ori
            (fun () => (cstr, Std.NoBindings))
            occs
            id;
          try (Control.focus 1 1 (fun () => try (Reflexivity)))
        | [|- _] => ()
        end
    );
    try typeclasses_eauto
).

Ltac2 Notation "Rewrite"
  ori(orient)
  cstr_with_bindings_th(thunk(seq(open_constr, with_bindings)))
  occs(occurrences)
  id(opt(seq("in", ident))) :=
rewrite_impl (Option.default Std.LTR ori) cstr_with_bindings_th occs id.

Fact forall_rewrite_lemma
  {T TT₁ TT₂} {f : forall x : T, TT₁ x}
  `(forall x, RewriteLemma (f x) (TT₂ x)) :
    RewriteLemma f (forall x, TT₂ x).
Proof.
  split.
  intros x.
  apply Rewrite.rewrite_lemma.
Defined.

Fact pointwise_relation_rewrite_lemma
  {T₁ T₂ R f g} {H₁ : pointwise_relation (B := T₂) T₁ R f g} :
    RewriteLemma H₁ (pointwise_relation T₁ R f g).
Proof.
  split.
  assumption.
Defined.

Hint Resolve forall_rewrite_lemma | 1 : rewrite_lemma_instances.

Hint Resolve pointwise_relation_rewrite_lemma | 0 : rewrite_lemma_instances.

Instance :
  forall {T₁ T₂} R₁ R₂,
    subrelation R₁ R₂ ->
      subrelation
        (pointwise_relation (B := T₂) T₁ R₁)
        (pointwise_relation T₁ R₂).
Proof.
  intros T₁ T₂ R₁ R₂ H₁ f g H₂ x.
  apply H₁.
  apply H₂.
Qed.