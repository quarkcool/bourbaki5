Require Export
  Bourbaki.Meta.Util.

Class ExfalsoRule T := {
  NewGoal : Type;
  exfalso_rule : NewGoal -> T
}.

Ltac2 exfalso_impl () :=
Control.enter (
  fun () =>
    refine '(Exfalso.exfalso_rule _);
    Control.enter (
      fun () =>
        lazy_match! goal with
        | [|- ExfalsoRule _] =>
          typeclasses_eauto
        | [|- @NewGoal _ ?cstr_inst] =>
          Util.unfold_instance_projection reference:(NewGoal) cstr_inst
        end
    )
).

Ltac2 Notation "Exfalso" := exfalso_impl ().