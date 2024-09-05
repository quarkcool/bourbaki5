Require Export
  Bourbaki.Logic.Truth.Syntax
  Coq.Lists.List.

Definition list_disjunction `{Logic.Truth.Syntax} 𝐀s :=
fold_right disjunction ⊥ 𝐀s.