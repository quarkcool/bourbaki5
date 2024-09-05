Require Export
  Bourbaki.Logic.Results.Meta.Logic.

Section Negation.
  Context `{Logic.Theory}.

  (* C11 *)
  Theorem double_removal 𝐑 :
    ⊢ 𝐑 ⇒ ¬¬𝐑.
  Proof.
    Apply Logic.excluded_middle.
  Qed.

  (* C12 *)
  Theorem rewriting 𝐑 𝐒 :
    ⊢ (𝐑 ⇒ 𝐒) ⇒ ¬𝐒 ⇒ ¬𝐑.
  Proof.
    Rewrite <- (Logic.disjunction_symmetry (¬𝐑)).
    Rewrite <- Negation.double_removal.
  Qed.

  #[export]
  Instance :
    Morphisms.Proper
      (ImplicationProof ==> Basics.flip ImplicationProof)
      negation
  | 0.
  Proof.
    Intros 𝐑 𝐒 H₁; unfold Basics.flip in *.
    Apply Negation.rewriting.
    Assumption.
  Qed.

  (* C16 *)
  Theorem doubling 𝐑 :
    ⊢ ¬¬𝐑 ⇒ 𝐑.
  Proof.
    Intros H₁ ?contra₁.
    repeat esplit;
      Assumption.
  Qed.
End Negation.