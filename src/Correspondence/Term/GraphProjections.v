Require Export
  Bourbaki.Correspondence.Notation
  Bourbaki.Correspondence.Term.Graph.

Section GraphProjections.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  (* première projection de G / ensemble de définition de G *)
  Definition first_projection (G : Graph) := {x | ∃ y, ❨x, y❩ ∈ G}.

  (* seconde projection de G / ensemble des valeurs de G *)
  Definition second_projection (G : Graph) := {y | ∃ x, ❨x, y❩ ∈ G}.
End GraphProjections.

Notation "pr₁⟨ G ⟩" := (first_projection G) : bourbaki_scope.

Notation "pr₂⟨ G ⟩" := (second_projection G) : bourbaki_scope.