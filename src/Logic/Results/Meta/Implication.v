Require Export
  Bourbaki.Formal.Results.Meta.Implication
  Bourbaki.Logic.Theory.

Module Implication.
  Section Implication.
    Context `{Logic.Theory}.

    #[export]
    Instance :
      forall 𝐀,
        Morphisms.Proper
          (ImplicationProof ==> ImplicationProof)
          (implication 𝐀)
    | 0.
    Proof.
      Intros 𝐀 𝐁 𝐂 H₁.
      Apply Logic.disjunction_rewriting_right.
      Assumption.
    Qed.

    #[export]
    Instance :
      forall 𝐀,
        Morphisms.Proper
          (ImplicationProof --> Basics.flip ImplicationProof)
          (implication 𝐀)
    | 0 := ltac2:(flip_morphism ()).

    (* C6 *)
    Theorem transitivity {𝐀 𝐁 𝐂} :
      (⊢ 𝐀 ⇒ 𝐁) -> (⊢ 𝐁 ⇒ 𝐂) -> ⊢ 𝐀 ⇒ 𝐂.
    Proof.
      Intros H₁ H₂.
      Rewrite <- H₂.
      Assumption.
    Qed.

    #[export]
    Instance :
      RelationClasses.Transitive ImplicationProof.
    Proof.
      Apply @Implication.transitivity.
    Qed.

    (* C8 *)
    Theorem reflexivity 𝐀 :
      ⊢ 𝐀 ⇒ 𝐀.
    Proof.
      Rewrite <- (Logic.disjunction_idempotence 𝐀) at 2.
      Apply Logic.disjunction_introduction_left.
    Qed.

    #[export]
    Instance :
      RelationClasses.Reflexive ImplicationProof | 0.
    Proof.
      Apply Implication.reflexivity.
    Qed.
  End Implication.
End Implication.
Export (hints) Implication.