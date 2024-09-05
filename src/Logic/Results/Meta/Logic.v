Require Export
  Bourbaki.Formal.Contradiction
  Bourbaki.Logic.Results.Meta.Disjunction
  Bourbaki.Meta.Tactic.Exfalso.

Section Logic.
  Context `{Logic.Theory}.

  Theorem ex_falso_quodlibet 𝐑 :
    Contradiction -> ⊢ 𝐑.
  Proof.
    Intros [𝐒 [H₁ H₂]].
    Apply (_ : ⊢ 𝐒 ⇒ 𝐑);
      Assumption.
  Qed.

  #[export]
  Instance :
    forall 𝐑, ExfalsoRule (⊢ 𝐑).
  Proof.
    Intros 𝐑.
    esplit.
    Apply Logic.ex_falso_quodlibet.
  Defined.

  (* C10 *)
  Theorem excluded_middle 𝐑 :
    ⊢ 𝐑 ∨ ¬𝐑.
  Proof.
    Apply Logic.disjunction_symmetry.
    Apply Implication.reflexivity.
  Qed.
End Logic.