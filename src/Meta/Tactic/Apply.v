Require Export
  Bourbaki.Meta.Util.

Create HintDb entailment_instances discriminated.

Class Entailment {T₁} (init : bool) (x : T₁) T₂ := {
  entails : T₂;
  dummy : unit
}.

Ltac2 solve_entailment () :=
unshelve (typeclasses_eauto with entailment_instances typeclass_instances).

Ltac2 apply_impl shelve_flag cstr_th :=
Control.enter (
  fun () =>
    refine '(Apply.entails (init := true)) > [|
      Control.refine cstr_th
    |
      solve_entailment ()
    ];
    Util.cleanup_post_tc_resolution ();
    if shelve_flag then
      Control.shelve_unifiable ()
    else
      ();
    Control.enter (fun () => simpl beta)
).

Ltac2 Notation "Apply" cstr_th(thunk(open_constr)) := apply_impl true cstr_th.

Ltac2 Notation "Simple" "Apply" cstr_th(thunk(open_constr)) :=
apply_impl false cstr_th.

Fact entailment_initialization {T₁ T₂} {x : T₁} `(Entailment _ false x T₂) :
  Entailment true x T₂.
Proof.
  repeat split.
  apply Apply.entails.
Defined.

Hint Resolve entailment_initialization | 0 : entailment_instances.

Fact forall_entailment
  {T₁ TT T₂} {f : forall x : T₁, TT x} {x : SolveLater _}
  `(Entailment _ false (f x) T₂) :
    Entailment false f T₂.
Proof.
  repeat split.
  Apply _.
Defined.

Fact self_entailment {T} (x : T) :
  Entailment false x T.
Proof.
  repeat split.
  exact x.
Defined.

Hint Extern 0 (Entailment false _ _) =>
  notypeclasses refine (self_entailment _) :
entailment_instances.

Hint Extern 1 (Entailment false _ _) =>
  notypeclasses refine (forall_entailment _) :
entailment_instances.

Hint Extern 0 (NotBothEvar ?x ?y) =>
  tryif is_evar x then
    tryif is_evar y then
      fail "Met evar in both cases"
    else
      exact_no_check tt
  else
    exact_no_check tt :
entailment_instances.

Hint Extern 0 (NotEvar ?x) =>
  tryif is_evar x then fail "Met evar" else exact_no_check tt :
entailment_instances.

Hint Extern 0 (SolveForSureLater _) => shelve : entailment_instances.

Hint Extern 0 (SolveLater _) => shelve : entailment_instances.

Hint Extern 0 (SolveOrShelve _) => shelve : entailment_instances.

Hint Extern 0 (Ununifiable ?x ?y) =>
  tryif unify x y then
    fail "Met unifiable terms"
  else
    exact_no_check tt :
entailment_instances.