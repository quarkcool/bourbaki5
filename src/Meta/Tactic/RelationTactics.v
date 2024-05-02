Require Export
  Bourbaki.Meta.Tactic.Plus
  Bourbaki.Meta.Util
  Coq.Classes.CRelationClasses
  Coq.Classes.RelationClasses.

#[export] Obligation Tactic := idtac.

Ltac2 reflexivity_impl () :=
Util.on_hidden_goal (
  fun () =>
    first [
      reflexivity
    |
      lazy_match! goal with
      | [|- ?f (?g _ _)] =>
        plus [
          apply (CRelationClasses.reflexivity (R := fun x y => $f ($g x y)) _)
        |
          apply (RelationClasses.reflexivity (R := fun x y => $f ($g x y)) _)
        ];
        Control.enter (
          fun () =>
            lazy_match! goal with
            | [|- CRelationClasses.Reflexive _] => typeclasses_eauto
            | [|- RelationClasses.Reflexive _] => typeclasses_eauto
            | [|- _] => ()
            end
        )
      end
    ]
).

Ltac2 Notation "Reflexivity" := reflexivity_impl ().

Ltac2 symmetry_impl () :=
Util.on_hidden_goal (
  fun () =>
    first [
      symmetry
    |
      lazy_match! goal with
      | [|- ?f (?g _ _)] =>
        plus [
          refine '(CRelationClasses.symmetry (R := fun x y => $f ($g x y)) _)
        |
          refine '(RelationClasses.symmetry (R := fun x y => $f ($g x y)) _)
        ];
        Control.enter (
          fun () =>
            lazy_match! goal with
            | [|- CRelationClasses.Symmetric _] => typeclasses_eauto
            | [|- RelationClasses.Symmetric _] => typeclasses_eauto
            | [|- _] => ()
            end
        )
      end
    ]
).

Ltac2 Notation "Symmetry" := symmetry_impl ().

Ltac2 transitivity_impl () :=
Util.on_hidden_goal (
  fun () =>
    match! goal with
    | [|- ?f _ _] =>
      plus [
        refine '(RelationClasses.transitivity (R := $f) _ _)
      |
        refine '(CRelationClasses.transitivity (R := $f) _ _)
      ];
      ()
    | [|- ?f (?g _ _)] =>
      plus [
        refine '(
          RelationClasses.transitivity (R := fun x y => $f ($g x y)) _ _
        )
      |
        refine '(
          CRelationClasses.transitivity (R := fun x y => $f ($g x y)) _ _
        )
      ];
      ()
    end;
    Control.enter (
      fun () =>
        lazy_match! goal with
        | [|- CRelationClasses.Transitive _] => typeclasses_eauto
        | [|- RelationClasses.Transitive _] => typeclasses_eauto
        | [|- _] => ()
        end
    );
    Control.shelve_unifiable ();
    Control.enter (
      fun () =>
        Std.simpl
          RedFlags.beta
          None
          { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences }
    )
).

Ltac2 Notation "Transitivity" := transitivity_impl ().