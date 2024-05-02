Require Export
  Bourbaki.Root
  Ltac2.Ltac2
  Ltac2.RedFlags.

Create HintDb goal_hiding_instances discriminated.
Hint Constants Opaque : goal_hiding_instances.

Class BoxedT T := box { unbox : T }.
Arguments box {_}.
Arguments unbox {_} : simpl never.

Class GoalHiding T := {
  HiddenGoal : Type;
  goal_hiding : HiddenGoal -> T
}.

Class Inhabited T := default : T.

Class Trivial {T} (x : T) := trivial_ : unit.

Definition no_hiding T : GoalHiding T := {| Util.goal_hiding := fun x => x |}.

Definition NotBothEvar {T₁ T₂} (x : T₁) (y : T₂) := unit.

#[local] Set Typeclasses Unique Instances.
Class NotEvar {T} (x : T) := not_evar : unit.

Definition SolveForSureLater (T : Type) := T.

Definition SolveLater (T : Type) := T.

Definition SolveOrShelve (T : Type) := T.

Instance trivial {T} : forall x, Trivial (T := T) x := fun _ => tt.

Definition Ununifiable {T} (x y : T) := unit.

Ltac2 cleanup_post_tc_resolution () :=
Control.enter (
  fun () =>
    lazy_match! goal with
    | [|- SolveForSureLater ?t] =>
      ltac1:(cstr |- change_no_check cstr) (Ltac1.of_constr t);
      typeclasses_eauto
    | [|- SolveLater ?t] =>
      ltac1:(cstr |- change_no_check cstr) (Ltac1.of_constr t);
      try typeclasses_eauto
    | [|- SolveOrShelve ?t] =>
      ltac1:(cstr |- change_no_check cstr) (Ltac1.of_constr t);
      first [typeclasses_eauto | Control.shelve ()]
    | [|- _] =>
      try typeclasses_eauto
    end
).

Ltac2 rec find_head_constant cstr :=
match Constr.Unsafe.kind cstr with
| Constr.Unsafe.App cstr _ => find_head_constant cstr
| Constr.Unsafe.Constant const _ => Some const
| _ => None
end.

Ltac2 hyp_unfold id :=
Std.eval_unfold [(Std.VarRef id, Std.AllOccurrences)] (Control.hyp id).

Ltac2 unfold_instance_projection ref_cls cstr_inst :=
match find_head_constant cstr_inst with
| Some const =>
  Std.unfold
    [
      (Std.ConstRef const, Std.AllOccurrences);
      (ref_cls, Std.AllOccurrences)
    ]
    {Std.on_hyps := None; Std.on_concl := Std.AllOccurrences}
| _ =>
  Control.throw
    (Tactic_failure
      (Some
        (Message.of_string
          "unfold_class_projection: Unable to find head constant"
        )
      )
    )
end.

#[warnings="-ltac2-unused-variable"]
Ltac2 on_hidden_goal tac :=
Control.enter (
  fun () =>
    let cstr := Control.goal () in
    refine '(Util.goal_hiding (T := $cstr) _);
    Control.enter (
      fun () =>
        lazy_match! goal with
        | [|- GoalHiding _] => typeclasses_eauto with goal_hiding_instances
        | [|- @HiddenGoal _ ?cstr_inst] =>
          unfold_instance_projection reference:(HiddenGoal) cstr_inst;
          lazy_match! goal with
          | [|- context f [Util.box ?x]] =>
            set (__hidden := Util.box $x);
            tac ();
            Control.enter (
              fun () =>
                Std.unfold
                  [
                    (reference:(&__hidden), Std.AllOccurrences);
                    (reference:(Util.unbox), Std.AllOccurrences)
                  ]
                  { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences };
                clear __hidden
            )
          | [|- _] => tac ()
          end
        end
  )
).

Hint Resolve no_hiding | 100 : goal_hiding_instances.

Hint Extern 0 (NotEvar ?x) =>
  tryif is_evar x then fail "Met evar" else exact_no_check tt :
typeclass_instances.