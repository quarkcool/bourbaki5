Require Export
  Bourbaki.Meta.Util.

Create HintDb introduction_pattern_instances discriminated.

Inductive PatternCategory :=
| simple_pattern
| complex_pattern
| fresh_pattern.

Class IntroductionPattern (cat : PatternCategory) T := {
  NewGoals : Type;
  introduction_pattern : NewGoals -> T
}.

Ltac2 intro_simple_pattern pat :=
refine '(Intros.introduction_pattern (cat := simple_pattern) _);
Control.enter (
  fun () =>
    lazy_match! goal with
    | [|- IntroductionPattern _ _] =>
      unshelve (
        typeclasses_eauto
          with introduction_pattern_instances typeclass_instances
      );
      Util.cleanup_post_tc_resolution ()
    | [|- @NewGoals _ _ ?cstr_inst] =>
      Util.unfold_instance_projection reference:(NewGoals) cstr_inst;
      Std.intros false [pat];
      try (split)
    end
);
Control.shelve_unifiable ();
try typeclasses_eauto.

Ltac2 intro_impl rec pat :=
first [
  Std.intros false [pat]
|
  match pat with
  | Std.IntroNaming (Std.IntroIdentifier _) => intro_simple_pattern pat
  | Std.IntroNaming (Std.IntroFresh id) =>
    refine '(Intros.introduction_pattern (cat := fresh_pattern) _);
    Control.enter (
      fun () =>
        lazy_match! goal with
        | [|- IntroductionPattern _ _] =>
          unshelve (
            typeclasses_eauto
              with introduction_pattern_instances typeclass_instances
          );
          Util.cleanup_post_tc_resolution ()
        | [|- @NewGoals _ _ ?cstr_inst] =>
          Util.unfold_instance_projection reference:(NewGoals) cstr_inst;
          rec [Std.IntroNaming (Std.IntroIdentifier id)];
          try (split)
        end
    );
    Control.shelve_unifiable ()
  | Std.IntroAction (Std.IntroWildcard) => intro_simple_pattern pat
  | Std.IntroAction (Std.IntroOrAndPattern (Std.IntroOrPattern patss)) =>
    refine '(Intros.introduction_pattern (cat := complex_pattern) _);
    Control.enter (
      fun () =>
        lazy_match! goal with
        | [|- IntroductionPattern _ _] =>
          unshelve (
            typeclasses_eauto
              with introduction_pattern_instances typeclass_instances
          );
          Util.cleanup_post_tc_resolution ()
        | [|- @NewGoals _ _ ?cstr_inst] =>
          Notations.dispatch0
            (fun () =>
              Util.unfold_instance_projection reference:(NewGoals) cstr_inst;
              repeat split)
            (List.map (fun pats () => rec pats) patss, None)
        end
    );
    Control.shelve_unifiable ();
    try typeclasses_eauto
  | _ =>
    Control.throw
      (Tactic_failure
        (Some (Message.of_string "Intros: Unhandled introduction pattern")))
  end
].

Ltac2 rec intros_impl pats :=
Control.enter (fun () => List.iter (intro_impl intros_impl) pats).

Ltac2 Notation "Intros" pats(intropatterns) := intros_impl pats.

Hint Extern 0 (SolveForSureLater _) => shelve : introduction_pattern_instances.

Hint Extern 0 (SolveLater _) => shelve : introduction_pattern_instances.

Hint Extern 0 (Ununifiable ?x ?y) =>
  tryif unify x y then
    fail "Met unifiable terms"
  else
    exact_no_check tt :
introduction_pattern_instances.