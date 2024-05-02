Require Export
  Bourbaki.Meta.Util.

Create HintDb entailment_instances discriminated.

Class Entailment (init : bool) T₁ {x : T₁} T₂ := {
  entails : T₂;
  dummy : unit
}.

Ltac2 solve_entailment () :=
ltac1:(
  unshelve (typeclasses eauto with entailment_instances typeclass_instances)
).

Ltac2 apply_impl shelve_flag cstr_th :=
Control.enter (
  fun () =>
    refine '(Apply.entails (init := true)) > [|
      Control.refine cstr_th
    |
      solve_entailment ()
    ];
    if shelve_flag then
      Control.shelve_unifiable ()
    else
      ();
    Util.cleanup_post_tc_resolution ()
).

Ltac2 Notation "Apply" cstr_th(thunk(open_constr)) := apply_impl true cstr_th.

Ltac2 Notation "Simple" "Apply" cstr_th(thunk(open_constr)) :=
apply_impl false cstr_th.

Definition entailment_initialization
  {T₁ x T₂} `(Entailment (x := x) false T₁ T₂) :
    Entailment (x := x) true T₁ T₂ :=
{| Apply.entails := Apply.entails; Apply.dummy := tt |}.

Hint Resolve entailment_initialization | 0 : entailment_instances.

Definition forall_entailment
  {T₁ TT} {f : forall x : T₁, TT x} {x : SolveLater _} {T₂}
  `(Entailment (x := f x) false (TT x) T₂) :
    Entailment (x := f) false (forall x, TT x) T₂.
Proof.
  repeat split.
  Apply _.
Defined.

Definition self_entailment {T} x :
  Entailment (x := x) false T T :=
{| Apply.entails := x; Apply.dummy := tt |}.

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

Hint Resolve trivial : entailment_instances.

Hint Extern 0 (Ununifiable ?x ?y) =>
  tryif unify x y then
    fail "Met unifiable terms"
  else
    exact_no_check tt :
entailment_instances.