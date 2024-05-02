Require Export
  Bourbaki.Meta.Tactic.RelationTactics
  Ltac2.Ref.

Create HintDb rewrite_lemma_instances discriminated.

Class RewriteLemma {T₁} (x : T₁) T₂ := { rewrite_lemma : T₂ }.

Ltac2 rewrite_impl ori cstr_th occs id :=
Util.on_hidden_goal (
  fun () =>
    refine '(let __rewrite_lemma := Rewrite.rewrite_lemma in _) > [|
      Control.refine cstr_th
    | |
      unshelve (
        typeclasses_eauto with rewrite_lemma_instances typeclass_instances
      )
    |];
    Control.enter (
      fun () =>
        lazy_match! goal with
        | [h := rewrite_lemma |- _] =>
          Std.cbn
            RedFlags.beta
            {
              Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHypTypeOnly)];
              Std.on_concl := Std.NoOccurrences
            };
          unshelve (
            Std.setoid_rewrite
              ori
              (fun () => (Control.hyp h, Std.NoBindings))
              occs
              id
          )
        | [|- _] => ()
        end
    );
    try typeclasses_eauto;
    let is_first := ref true in
    Control.enter (
      fun () =>
        lazy_match! goal with
        | [h := Rewrite.rewrite_lemma |- _] =>
          Std.clear [h];
          simpl beta;
          if Ref.get is_first then
            try (Reflexivity);
            Ref.set is_first false
          else
            ()
        | [|- _] => ()
        end
    )
).

Ltac2 Notation "Rewrite"
  ori(orient)
  cstr_th(thunk(open_constr))
  occs(occurrences)
  id(opt(seq("in", ident))) :=
rewrite_impl (Option.default Std.LTR ori) cstr_th occs id.

Fact eq_rewrite_lemma {T} {x y : T} (H₁ : x = y) :
  RewriteLemma H₁ (x = y).
Proof.
  split.
  assumption.
Defined.

Fact forall_relation_rewrite_lemma
  {T F R f g} {H₁ : forall_relation (A := T) (P := F) R f g} :
    RewriteLemma H₁ (forall_relation R f g).
Proof.
  split.
  assumption.
Defined.

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

Hint Resolve eq_rewrite_lemma | 0 : rewrite_lemma_instances.

Hint Resolve forall_relation_rewrite_lemma | 0 : rewrite_lemma_instances.

Hint Resolve forall_rewrite_lemma | 1 : rewrite_lemma_instances.

Hint Resolve pointwise_relation_rewrite_lemma | 2 : rewrite_lemma_instances.

Instance :
  forall {T F R₁ R₂},
    RelationClasses.subrelation
      R₁
      (forall_relation (A := T) (P := F) (fun x => Basics.flip (R₂ x)))
    ->
      RelationClasses.subrelation R₁ (Basics.flip (forall_relation R₂)).
Proof.
  intros T F R₁ R₂ H₁ f g H₂ x.
  apply H₁.
  assumption.
Qed.

Instance :
  forall {T₁ T₂ R₁ R₂},
    RelationClasses.subrelation R₁ R₂ ->
      RelationClasses.subrelation
        (pointwise_relation (B := T₂) T₁ R₁)
        (pointwise_relation T₁ R₂).
Proof.
  intros T₁ T₂ R₁ R₂ H₁ f g H₂ x.
  apply H₁.
  apply H₂.
Qed.

Instance :
  forall {T₁ T₂ R₁ R₂},
    RelationClasses.subrelation
      R₁
      (pointwise_relation (B := T₂) T₁ (Basics.flip R₂))
    ->
      RelationClasses.subrelation R₁ (Basics.flip (pointwise_relation T₁ R₂)).
Proof.
  intros T₁ T₂ R₁ R₂ H₁ f g H₂ x.
  apply H₁.
  assumption.
Qed.

Instance :
  forall {T F R},
    (forall x, RelationClasses.Symmetric (R x)) ->
      RelationClasses.Symmetric (forall_relation (A := T) (P := F) R).
Proof.
  intros T F R H₁ f g H₂ x.
  apply H₁.
  apply H₂.
Qed.