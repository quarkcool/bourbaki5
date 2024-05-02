Require Export
  Bourbaki.Root
  Ltac2.Ltac2.

Ltac2 rec change_impl cstr_th :=
Control.enter (
  fun () =>
    refine '(@id ltac2:(Control.refine cstr_th) _);
    simpl beta
).

Ltac2 Notation "Change" cstr(thunk(open_constr)) := change_impl cstr.