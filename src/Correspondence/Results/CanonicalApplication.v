Require Export
  Bourbaki.Correspondence.Correspondence.CanonicalApplication
  Bourbaki.Correspondence.Relation.Injectivity
  Bourbaki.Correspondence.Results.Diagonal
  Bourbaki.Correspondence.Results.TermFunction.

Section CanonicalApplication.
  Context `{Set_.Theory}.

  Theorem graphₑ {X Y} `(!X ⊢⊂ Y) :
    ⊢ canonical_application _ = Δ X.
  Proof.
    Apply Graph.equalityₑ.
    Intros x y.
    solve [Rewrite CoupleMembershipEquivalenceProof.proof].
  Qed.

  Theorem injectivity {X Y} `(!X ⊢⊂ Y) :
    ⊢ is_injective (canonical_application _).
  Proof.
    Intros x H₁ y H₂;
      Change (⊢ _ ⇒ ¬_).
    Rewrite ValueEqualityProof.proof.
  Qed.
End CanonicalApplication.