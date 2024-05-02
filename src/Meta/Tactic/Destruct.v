Require Export
  Bourbaki.Meta.Tactic.Revert.

Create HintDb destructible_instances discriminated.

Class Destructible (T : Type) := { dummy : unit }.

Definition DestructibleType {T} `{Destructible T} := T.

Ltac2 destruct_impl cstr_th pats :=
Control.enter (
  fun () =>
    refine '(
      let __destruct_lemma : DestructibleType :=
        Apply.entails
          (init := false)
          (x :=
            ltac2:(
              Control.refine cstr_th;
              try typeclasses_eauto
            )
          )
      in
      _
    );
    Control.enter (
      fun () =>
        lazy_match! goal with
        | [|- Destructible _] => typeclasses_eauto with destructible_instances
        | [|- Entailment _ _ _] =>
          unfold DestructibleType;
          solve_entailment ();
          Util.cleanup_post_tc_resolution ();
          ltac1:(revgoals)
        | [h := Apply.entails |- _] =>
          Std.unfold
            [(reference:(DestructibleType), Std.AllOccurrences)]
            {
              Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHypTypeOnly)];
              Std.on_concl := Std.NoOccurrences
            };
          revert_impl h;
          intros_impl pats
        | [|- _] => ()
        end
    );
    Control.shelve_unifiable ()
).

Ltac2 Notation
  "Destruct" cstr_th(thunk(open_constr)) "as" pats(intropatterns) :=
destruct_impl cstr_th pats.