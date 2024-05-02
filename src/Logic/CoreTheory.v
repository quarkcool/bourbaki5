Require Export
  Bourbaki.Formal.Theory.

Module Logic.
  Class CoreTheory `{Formal.Theory} := {
    disjunction_idempotence :
      forall 𝐀, ⊢ 𝐀 ∨ 𝐀 ⇒ 𝐀;
    disjunction_introduction_left :
      forall 𝐀 𝐁, ⊢ 𝐀 ⇒ 𝐀 ∨ 𝐁;
    disjunction_commutativity :
      forall 𝐀 𝐁, ⊢ 𝐀 ∨ 𝐁 ⇒ 𝐁 ∨ 𝐀;
    disjunction_rewriting_right :
      forall 𝐀 𝐁 𝐂, ⊢ (𝐀 ⇒ 𝐁) ⇒ 𝐂 ∨ 𝐀 ⇒ 𝐂 ∨ 𝐁
  }.
End Logic.