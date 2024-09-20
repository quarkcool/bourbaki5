Require Export
  Bourbaki.Correspondence.Relation.FunctionEssence.

Section Application.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  (* application de X dans Y *)
  Structure Application X Y := {
    set :> Term;

    graph_essence :: IsGraph set;
    #[export, canonical=no] function_essence :: IsFunction set X Y
  }.

  Canonical application {F X Y} `(!IsGraph F) `(!IsFunction F X Y) :=
  {| set := F |}.

  Coercion as_graph {X Y} (f : Application X Y) := {| Graph.set := f |}.
End Application.

Infix "→" := Application : type_scope.

Notation "↑ F" := (application (F := F) _ _) : bourbaki_scope.