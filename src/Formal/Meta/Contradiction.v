Require Export
  Bourbaki.Formal.Theory.

(* théorie contradictoire *)
Definition Contradiction `{Formal.Theory} := {𝐀 & ((⊢ 𝐀) * (⊢ ¬𝐀))%type}.