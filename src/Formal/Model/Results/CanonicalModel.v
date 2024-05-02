Require Export
  Bourbaki.Formal.Model.Proof
  Bourbaki.Formal.Theory
  Bourbaki.Meta.Tactic.Apply.

Section CanonicalModel.
  Context `{𝒯 : Theory}.

  #[export]
  Instance Th :
    Formal.Theory.
  Proof.
    refine '{| Formal.Proof := fun 𝐀 => 𝒯 ⊢ 𝐀 |}.
    Apply @Proof.syllogism.
  Defined.
End CanonicalModel.
Canonical Th.