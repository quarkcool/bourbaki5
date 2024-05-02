Require Export
  Bourbaki.Meta.Tactic.RelationTactics
  Bourbaki.Util.Classes.CMorphisms.

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

Definition forall_relation_rewrite_lemma
  {T P R x y} (H₁ : CMorphisms.forall_relation R x y) :
    RewriteLemma H₁ (CMorphisms.forall_relation (A := T) (P := P) R x y) :=
{| Rewrite.rewrite_lemma := H₁ |}.

Definition forall_rewrite_lemma
  {T TT₁} {f : forall x : T, TT₁ x} {TT₂}
  `(forall x, RewriteLemma (f x) (TT₂ x)) :
    RewriteLemma f (forall x, TT₂ x) :=
{| Rewrite.rewrite_lemma := fun x => rewrite_lemma |}.

Definition pointwise_relation_rewrite_lemma
  {T₁ T₂ R x y} (H₁ : CMorphisms.pointwise_relation T₁ R x y) :
    RewriteLemma H₁ (CMorphisms.pointwise_relation (B := T₂) T₁ R x y) :=
{| Rewrite.rewrite_lemma := H₁ |}.

Hint Resolve forall_relation_rewrite_lemma | 0 : rewrite_lemma_instances.

Hint Resolve forall_rewrite_lemma | 1 : rewrite_lemma_instances.

Hint Resolve pointwise_relation_rewrite_lemma | 0 : rewrite_lemma_instances.