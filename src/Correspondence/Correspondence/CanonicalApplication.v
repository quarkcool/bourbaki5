Require Export
  Bourbaki.Correspondence.Correspondence.TermFunction.

Section CanonicalApplication.
  Context `{Set_.Theory}.
  Context {X Y : Term} `(!X ⊢⊂ Y).

  #[export]
  Instance :
    set_by_replacement (fun x => x) X ⊢⊂ Y.
  Proof.
    Change (⊢ ∀ y, _).
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite Equality.commutativity.
    Rewrite Existence.of_equalₑ.
    Assumption.
  Qed.

  (* application canonique de X dans Y / injection canonique de X dans Y *)
  Definition canonical_application : X → Y := x ∈ X ↦ x ∈ Y.
End CanonicalApplication.