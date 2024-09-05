Require Export
  Bourbaki.Formal.Results.Meta.Implication
  Bourbaki.Logic.Theory.

Section Implication.
  Context `{Logic.Theory}.

  #[export]
  Instance :
    forall 𝐑,
      Morphisms.Proper
        (ImplicationProof --> Basics.flip ImplicationProof)
        (implication 𝐑)
  | 0.
  Proof.
    Intros 𝐑 𝐓 𝐒 H₁; unfold Basics.flip in *.
    Apply Logic.disjunction_rewriting_right.
    Assumption.
  Qed.
End Implication.