Require Export
  Bourbaki.Correspondence.Results.Meta.RelationGraph
  Bourbaki.Correspondence.Term.Correspondence
  Bourbaki.Set.InclusionProof.

Section RelationCorrespondence.
  Context `{
    Logic.Truth.Theory, !Logic.Theory, !Quantification.Theory,
    !Equality.Syntax, !Set_.Syntax
  }.
  Context
    {𝐑} {X Y : Term} `(!HasGraph 𝐑)
    `(!pr₁⟨{❨x, y❩ | 𝐑 x y}⟩ ⊢⊂ X) `(!pr₂⟨{❨x, y❩ | 𝐑 x y}⟩ ⊢⊂ Y).

  #[export]
  Instance :
    IsCorrespondence {❨x, y❩ | 𝐑 x y} X Y.
  Proof.
    Intros [|];
      Assumption.
  Qed.

  (* correspondance entre X et Y définie par la relation 𝐑 *)
  Definition relation_correspondence : Correspondence X Y := {❨x, y❩ | 𝐑 x y}.
End RelationCorrespondence.