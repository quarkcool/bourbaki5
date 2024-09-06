Require Export
  Bourbaki.Formal.Theory.

Module Logic.
  Class Theory `{Formal.Theory} := {
    (* S1 *)
    disjunction_idempotence :
      forall 𝐑, ⊢ 𝐑 ∨ 𝐑 ⇒ 𝐑;
    (* S2 *)
    disjunction_introduction_left :
      forall 𝐑 𝐒, ⊢ 𝐑 ⇒ 𝐑 ∨ 𝐒;
    (* S3 *)
    disjunction_symmetry :
      forall 𝐑 𝐒, ⊢ 𝐑 ∨ 𝐒 ⇒ 𝐒 ∨ 𝐑;
    (* S4 *)
    disjunction_rewriting_right :
      forall 𝐒 𝐓 𝐑, ⊢ (𝐒 ⇒ 𝐓) ⇒ 𝐑 ∨ 𝐒 ⇒ 𝐑 ∨ 𝐓
  }.
End Logic.