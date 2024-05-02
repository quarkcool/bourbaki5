Require Export
  Bourbaki.Meta.Tactic.Apply.

Ltac2 rec handle_hyps hyps :=
match hyps with
| (id, _, _) :: hyps =>
  Control.plus
    (fun () => let cstr := Control.hyp id in solve [Apply $cstr])
    (fun _ => handle_hyps hyps)
| [] => Control.backtrack_tactic_failure "Found no suitable assumption"
end.

Ltac2 assumption_impl () :=
Control.enter (fun () => handle_hyps (List.rev (Control.hyps ()))).

Ltac2 Notation "Assumption" := assumption_impl ().