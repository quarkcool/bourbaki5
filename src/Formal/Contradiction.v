Require Export
  Bourbaki.Formal.Theory.

Definition Contradiction `{Formal.Theory} := exists 𝐀, ((⊢ 𝐀) * ⊢ ¬𝐀)%type.