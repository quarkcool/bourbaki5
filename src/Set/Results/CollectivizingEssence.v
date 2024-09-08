Require Export
  Bourbaki.Equality.Relation.FunctionalEssence
  Bourbaki.Set.Relation.CollectivizingEssence
  Bourbaki.Set.Results.Set.

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
End CollectivizingEssence.