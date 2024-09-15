Require Export
  Bourbaki.Correspondence.Relation.CorrespondenceEssence
  Bourbaki.Logic.Results.Meta.Conjunction.

Section Correspondence.
  Context `{Logic.Truth.Theory, !Logic.Theory, !Equality.Syntax, !Set_.Syntax}.

  Theorem first_projection_subset_essence {G X Y} `(!IsCorrespondence G X Y) :
    ⊢ pr₁⟨G⟩ ⊂ X.
  Proof.
    Apply (CorrespondenceEssence.correspondence_essence (G := G)).
  Qed.

  Theorem second_projection_subset_essence {G X Y} `(!IsCorrespondence G X Y) :
    ⊢ pr₂⟨G⟩ ⊂ Y.
  Proof.
    Apply (CorrespondenceEssence.correspondence_essence (G := G)).
  Qed.
End Correspondence.