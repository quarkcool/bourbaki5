Require Export
  Bourbaki.Meta.Tactic.Assumption
  Bourbaki.Meta.Tactic.Intros.

Create HintDb revert_instances discriminated.

Class Revert {T₁} (x : T₁) T₂ := {
  NewGoals : Type;
  revert : NewGoals -> T₂
}.

Ltac2 revert_impl id :=
Control.enter (
  fun () =>
    let cstr := Control.hyp id in
    refine '(Revert.revert (x := $cstr) _);
    Control.enter (
      fun () =>
        lazy_match! goal with
        | [|- Revert _ _] =>
          typeclasses_eauto with revert_instances typeclass_instances
        | [|- @NewGoals _ _ _ ?cstr_inst] =>
          Util.unfold_instance_projection reference:(NewGoals) cstr_inst;
          Std.clear [id]
        end
    )
).

Ltac2 Notation "Revert" id(ident) := revert_impl id.

Definition meta_revert {T₁} (x : T₁) T₂ :
  Revert x T₂.
Proof.
  refine '{| Revert.NewGoals := T₁ -> T₂ |}.
  Intros f.
  Apply f.
  Assumption.
Defined.

Hint Resolve meta_revert | 1 : revert_instances.