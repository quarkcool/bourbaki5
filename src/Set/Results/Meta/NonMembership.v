Require Export
  Bourbaki.Set.Relation.NonMembership
  Bourbaki.Set.Results.Meta.Inclusion.

Module NonMembership.
  Section NonMembership.
    Context `{Quantification.Theory, !Equality.Syntax, !Set_.Syntax}.

    #[export]
    Instance :
      forall x,
        Morphisms.Proper
          (InclusionProof --> ImplicationProof)
          (non_membership x)
    | 0.
    Proof.
      Intros x Y X H₁; unfold Basics.flip in *.
      unfold non_membership.
      Rewrite H₁.
    Qed.

    #[export]
    Instance :
      forall x,
        Morphisms.Proper
          (InclusionProof ==> Basics.flip ImplicationProof)
          (non_membership x)
    | 0 := ltac2:(flip_morphism ()).
  End NonMembership.
End NonMembership.
Export (hints) NonMembership.