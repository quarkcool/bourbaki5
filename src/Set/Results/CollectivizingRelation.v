Require Export
  Bourbaki.Equality.Relation.SingleValuedRelation
  Bourbaki.Equality.Results.Theory
  Bourbaki.Set.Relation.CollectivizingRelation
  Bourbaki.Set.Relation.NonMembership
  Bourbaki.Set.Results.Equality.

Import Proof.TheoryHidingNotation.

Section CollectivizingRelation.
  Context `(SetTheory).

  #[export]
  Instance :
    forall y, CollectivizingRelation 𝒯 (∈ y).
  Proof.
    Intros y 𝒯' H₁ [x].
    Reflexivity.
  Defined.

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

  (* C49 *)
  #[export]
  Instance :
    forall {𝐑} `(!CollectivizingRelation 𝒯 𝐑),
      FunctionalRelation 𝒯 (fun y => ∀ x, x ∈ y ⇔ 𝐑 x).
  Proof.
    Intros 𝐑 H₁ 𝒯' H₂ [|].
    { Apply CollectivizingRelation.collectivizing_essence. }
    { Apply SingleValuedRelation.single_valued_essence. }
  Defined.

  Theorem russell_paradox :
    𝒯 ⊢ ¬Coll (fun x => x ∉ x).
  Proof.
    Intros [y contra₁].
    Apply Equivalence.fundamental_impossibility.
    Assumption.
  Defined.
End CollectivizingRelation.