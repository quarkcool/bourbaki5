Require Export
  Bourbaki.Correspondence.Relation.CorrespondenceEssence.

Section Correspondence.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  Structure Correspondence X Y := {
    (* graphe [d'une correspondance] *)
    set :> Term;

    #[export, canonical=no] graph_essence :: IsGraph set;
    #[export, canonical=no] correspondence_essence :: IsCorrespondence set X Y
  }.

  Canonical correspondence {G X Y} `(!IsGraph G) `(!IsCorrespondence G X Y) :=
  {| set := G |}.

  Coercion as_graph {X Y} (Γ : Correspondence X Y) := {| Graph.set := Γ |}.
End Correspondence.

Arguments graph {_ _ _ _ _ _}.
Arguments correspondence_essence {_ _ _ _ _ _}.

Notation "↑ G" := (correspondence (G := G) _ _) : bourbaki_scope.