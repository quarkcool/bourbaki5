Require Export
  Bourbaki.Set.Results.SetByReplacement
  Bourbaki.Set.Term.Couple
  Bourbaki.Set.Term.SetByReplacement.

Section Product.
  Context `{Set_.Theory}.

  (* Th_E_II_2__1 *)
  Theorem collectivizing_essence :
    ⊢ ∀ X Y, Coll (fun z => ∃ x y, z = ❨x, y❩ ∧ x ∈ X ∧ y ∈ Y).
  Proof.
    Intros X Y.
    Rewrite Conjunction.associativity.
    Rewrite <- (fun _ => Conjunction.commutativity (_ ∈ X)).
    Rewrite <- Conjunction.associativity.
    Rewrite Existence.conjunct_extraction_left;
      Change (⊢ Coll (fun z => ∃ x, _ ∧ ∃ y, _)).
    Apply Set_.selection_union.
    Intros x [z].
    Apply (
      MembershipEquivalenceProof.proof (set_by_replacement (fun y => ❨x, y❩) Y)
    ).
  Qed.

  #[export]
  Instance :
    forall X Y, IsCollectivizing (fun z => ∃ x y, z = ❨x, y❩ ∧ x ∈ X ∧ y ∈ Y).
  Proof.
    Intros X Y.
    Apply Product.collectivizing_essence.
  Qed.
End Product.