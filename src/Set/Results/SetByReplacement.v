Require Export
  Bourbaki.Set.Results.Meta.CollectivizingEssence
  Bourbaki.Set.Results.Singleton.

Section SetByReplacement.
  Context `{Set_.Theory}.

  (* C53 *)
  #[export]
  Instance :
    forall 𝐓 X, IsCollectivizing (fun y => ∃ x, y = 𝐓 x ∧ x ∈ X).
  Proof.
    Intros 𝐓 Y;
      Change (IsCollectivizing (fun x => ∃ y, _)).
    Rewrite Conjunction.commutativity.
    Apply Set_.selection_union.
    Intros y [x H₁].
    Apply (MembershipEquivalenceProof.proof {𝐓 y,}).
    Assumption.
  Qed.
End SetByReplacement.