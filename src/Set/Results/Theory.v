Require Export
  Bourbaki.Quantification.Results.Meta.Universality
  Bourbaki.Set.Theory.

Import Proof.TheoryHidingNotation.

Module Set_.
  Section Set_.
    Context `(SetTheory).

    (* axiome de l'ensemble à deux éléments *)
    #[export]
    Instance :
      forall x y, CollectivizingRelation 𝒯 (fun z => z = x ∨ z = y).
    Proof.
      Intros x y 𝒯' H₁.
      Apply (
        Universality.elimination _ (fun y => Coll (fun z => z = x ∨ z = y))
      ).
      Apply (
        Universality.elimination _ (fun x => ∀ y, Coll (fun z => z = x ∨ z = y))
      ).
      Apply (StrongerTheoryEssence.weaker_explicit_axiom (𝒯₁ := Set_.Theory)).
      right.
      left.
      Reflexivity.
    Defined.

    (* axiome d'extensionalité *)
    Theorem extensionality :
      𝒯 ⊢ ∀ x y, x ⊂ y ⇒ y ⊂ x ⇒ x = y.
    Proof.
      Apply StrongerTheoryEssence.weaker_explicit_axiom.
      left.
      Reflexivity.
    Defined.
  End Set_.
End Set_.
Export (hints) Set_.