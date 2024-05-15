Require Export
  Bourbaki.Equality.Relation.SingleValuedRelation
  Bourbaki.Set.Results.Equality.

Import Proof.TheoryHidingNotation.

Section CollectivizingRelation.
  Context `(SetTheory).

  (* C48 *)
  #[export]
  Instance :
    forall 𝐑, SingleValuedRelation 𝒯 (fun y => ∀ x, x ∈ y ⇔ 𝐑 x).
  Proof.
    Intros 𝐑 𝒯' H₁ y₁ H₂ y₂ H₃.
    Apply Equality.alternative_definition.
    Intros z.
    Rewrite H₂.
    Rewrite H₃.
  Defined.
End CollectivizingRelation.