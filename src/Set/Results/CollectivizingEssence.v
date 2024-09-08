Require Export
  Bourbaki.Set.Results.CollectivizingSubset.

Section CollectivizingEssence.
  Context `{Set_.Theory}.

  (* Exa_E_II_1_4__1 *)
  #[export]
  Instance :
    forall X, IsCollectivizing (fun x => x ∈ X).
  Proof.
    Intros X [x].
    Reflexivity.
  Qed.

  (* C49 *)
  #[export]
  Instance :
    forall {𝐑} `(!IsCollectivizing 𝐑),
      IsFunctional (fun X => ∀ x, x ∈ X ⇔ 𝐑 x).
  Proof.
    Intros 𝐑 H₁ [|].
    Assumption.
  Qed.

  (* C52 *)
  Theorem from_container_set 𝐑 X :
    (forall x, ⊢ 𝐑 x ⇒ x ∈ X) -> IsCollectivizing 𝐑.
  Proof.
    Intros H₁;
      Change (IsCollectivizing (fun _ => _)).
    Rewrite <- Conjunction.operand_removal_right.
    Assumption.
  Qed.
End CollectivizingEssence.