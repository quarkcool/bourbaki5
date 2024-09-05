Require Export
  Bourbaki.Formal.Theory.

Module Logic.
  Class Theory `{Formal.Theory} := {
    (* S1 *)
    disjunction_idempotence :
      forall 𝐀, ⊢ 𝐀 ∨ 𝐀 ⇒ 𝐀;
    (* S2 *)
    disjunction_introduction_left :
      forall 𝐀 𝐁, ⊢ 𝐀 ⇒ 𝐀 ∨ 𝐁;
    (* S3 *)
    disjunction_symmetry :
      forall 𝐀 𝐁, ⊢ 𝐀 ∨ 𝐁 ⇒ 𝐁 ∨ 𝐀;
    (* S4 *)
    disjunction_rewriting_right :
      forall 𝐁 𝐂 𝐀, ⊢ (𝐁 ⇒ 𝐂) ⇒ 𝐀 ∨ 𝐁 ⇒ 𝐀 ∨ 𝐂;

    deduction :
      forall {𝐀 𝐁}, ((⊢ 𝐀) -> ⊢ 𝐁) -> ⊢ 𝐀 ⇒ 𝐁
  }.
End Logic.