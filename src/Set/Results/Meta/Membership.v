Require Export
  Bourbaki.Equality.Results.Meta.Truth
  Bourbaki.Quantification.Results.Meta.Universality
  Bourbaki.Set.InclusionProof.

Module Membership.
  Section Membership.
    Context `{Quantification.Theory, !Equality.Syntax, !Set_.Syntax}.

    #[export]
    Instance :
      forall x,
        Morphisms.Proper (InclusionProof ==> ImplicationProof) (membership x)
    | 0.
    Proof.
      Intros x X Y H₁.
      Assumption.
    Qed.

    #[export]
    Instance :
      forall x,
        Morphisms.Proper
          (InclusionProof --> Basics.flip ImplicationProof)
          (membership x)
    | 0 := ltac2:(flip_morphism ()).
  End Membership.
End Membership.
Export (hints) Membership.