Require Export
  Bourbaki.Set.Relation.Emptiness
  Bourbaki.Set.Results.Meta.NonMembership.

Module Emptiness.
  Section Emptiness.
    Context `{Quantification.Theory, !Equality.Syntax, !Set_.Syntax}.

    #[export]
    Instance :
      Morphisms.Proper (InclusionProof --> ImplicationProof) is_empty | 0.
    Proof.
      Intros Y X H₁; unfold Basics.flip in *.
      unfold is_empty.
      Rewrite H₁.
    Qed.

    #[export]
    Instance :
      Morphisms.Proper
        (InclusionProof ==> Basics.flip ImplicationProof)
        is_empty
    | 0 := ltac2:(flip_morphism ()).
  End Emptiness.
End Emptiness.
Export (hints) Emptiness.