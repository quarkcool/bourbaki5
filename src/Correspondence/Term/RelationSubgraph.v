Require Export
  Bourbaki.Correspondence.Term.RelationGraph.

Definition relation_subgraph `{Set_.Syntax} 𝐑 X :=
{❨x, y❩ | 𝐑 x y ∧ ❨x, y❩ ∈ X}.

Notation "{❨ x , y ❩ ∈ X | 𝐑 }" :=
  (relation_subgraph (fun x y => 𝐑) X) :
bourbaki_scope.