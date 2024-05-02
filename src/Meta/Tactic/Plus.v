Require Export
  Bourbaki.Root
  Ltac2.Ltac2.

Ltac2 rec plus_impl tacs tac :=
match tacs with
| [] => Control.zero (Tactic_failure None)
| tac' :: tacs =>
  Control.enter (
    fun () =>
      Control.plus (fun () => tac' (); tac ()) (fun _ => plus_impl tacs tac)
  )
end.

Ltac2 Notation
  "plus" "[" tacs(list0(thunk(tactic(6)), "|")) "]" ";" tac(thunk(tactic(6))) :=
plus_impl tacs tac.