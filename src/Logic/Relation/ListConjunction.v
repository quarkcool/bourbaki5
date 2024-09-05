Require Export
  Bourbaki.Logic.Relation.Conjunction
  Bourbaki.Logic.Truth.Syntax
  Coq.Lists.List.

Definition list_conjunction `{Logic.Truth.Syntax} 𝐀s :=
fold_right conjunction ⊤ 𝐀s.