Require Export
  Bourbaki.Logic.Relation.Conjunction
  Bourbaki.Truth.Syntax
  Coq.Lists.List.

Export ListNotations.

Fixpoint list_conjunction `{Truth.Syntax} 𝐀s :=
match 𝐀s with
| [] => ⊤
| 𝐀 :: 𝐀s => 𝐀 ∧ list_conjunction 𝐀s
end.
Hint Transparent list_conjunction : introduction_pattern_instances.