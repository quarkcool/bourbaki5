Require Export
  Bourbaki.Set.Results.Meta.CollectivizingSubset
  Bourbaki.Set.Results.Meta.NonMembership
  Bourbaki.Set.Term.Complement.

Module Complement.
  Section Complement.
    Context `{Set_.Theory}.

    #[export]
    Instance :
      forall x,
        Morphisms.Proper (InclusionProof --> InclusionProof) (complement x)
    | 0.
    Proof.
      Intros X B A H₁; unfold Basics.flip in *.
      unfold complement.
      Rewrite H₁.
    Qed.

    #[export]
    Instance :
      forall x,
        Morphisms.Proper
          (InclusionProof ==> Basics.flip InclusionProof)
          (complement x)
    | 0 := ltac2:(flip_morphism ()).
  End Complement.
End Complement.
Export (hints) Complement.