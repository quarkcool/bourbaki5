Require Export
  Bourbaki.Correspondence.Notation
  Bourbaki.Correspondence.Relation.GraphEssence.

(* graphe de 𝐑 / ensemble représentatif de 𝐑 *)
Definition relation_graph `{Set_.Syntax} 𝐑 :=
τ G, is_graph G ∧ ∀ x y, 𝐑 x y ⇔ ❨x, y❩ ∈ G.

Notation "{❨ x , y ❩ | 𝐑 }" :=
  (relation_graph (fun x y => 𝐑)) :
bourbaki_scope.