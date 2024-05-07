Require Export
  Bourbaki.Logic.Results.All
  Bourbaki.Quantification.Results.Meta.Rewriting.

Section TypicalUniversality.
  Context `(QuantifiedTheory).

  (* C35 *)
  Theorem alternative_definition 𝐑 𝐒 :
    𝒯 ⊢ (∀ x ⟨ 𝐑 ⟩, 𝐒 x) ⇔ ¬∃ x ⟨ 𝐑 ⟩, ¬𝐒 x.
  Proof.
    unfold TypicalExistence.typical_existence.
    Rewrite <- Implication.negationₑ.
  Defined.
End TypicalUniversality.