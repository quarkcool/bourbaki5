Require Export
  Bourbaki.Correspondence.Relation.GraphEssence
  Bourbaki.Formal.CoercibleTerm.

Section Graph.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  Structure Graph := {
    set :> Term;
    #[export, canonical=no] graph_essence :: IsGraph set
  }.
  Canonical Graph_ := {| coercion := fun x => set x |}.

  Canonical graph {G} `(!IsGraph G) := {| set := G |}.
End Graph.

Notation "↑ G" := (graph (G := G) _) : bourbaki_scope.