Require Export
  Bourbaki.Falsity.Syntax
  Coq.Lists.List.

Export ListNotations.

Fixpoint list_disjunction `{Falsity.Syntax} 𝐀s :=
match 𝐀s with
| [] => ⊥
| 𝐀 :: 𝐀s => 𝐀 ∨ list_disjunction 𝐀s
end.