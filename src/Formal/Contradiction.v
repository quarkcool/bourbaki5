Require Export
  Bourbaki.Formal.Theory.

Definition Contradiction `{Formal.Theory} := exists 𝐑, ((⊢ 𝐑) * ⊢ ¬𝐑)%type.