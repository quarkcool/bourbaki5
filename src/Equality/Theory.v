Require Export
  Bourbaki.Equality.Syntax
  Bourbaki.Logic.Relation.Equivalence
  Bourbaki.Quantification.Relation.Universality
  Bourbaki.Quantification.Theory.

Module Equality.
  Class Theory `{Quantification.Theory, !Equality.Syntax} := {
    (* S6 *)
    relation_rewriting :
      forall x y 𝐑, ⊢ x = y ⇒ (𝐑 x ⇔ 𝐑 y);
    (* S7 *)
    tau_abstraction_extensionality :
      forall 𝐑 𝐒, ⊢ (∀ x, 𝐑 x ⇔ 𝐒 x) ⇒ (τ x, 𝐑 x) = τ x, 𝐒 x
  }.
End Equality.