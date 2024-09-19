Require Export
  Bourbaki.Correspondence.Relation.SymmetricGraphEssence
  Bourbaki.Correspondence.Results.Diagonal
  Bourbaki.Correspondence.Results.Product
  Bourbaki.Correspondence.Results.ReverseGraph
  Bourbaki.Set.Results.Meta.Emptiness.

Module Diagonal.
  Section Diagonal.
    Context `{Set_.Theory}.

    Theorem symmetry :
      ⊢ ∀ X, is_symmetric_graph (Δ X).
    Proof.
      Rewrite Graph.equalityₑ.
      Intros X x y.
      do 2 (Rewrite CoupleMembershipEquivalenceProof.proof).
      Rewrite (fun x X => Conjunction.commutativity (x ∈ X)).
      Rewrite Equality.commutativity at 1.
      Apply (Equality.as_conjunct_leftₑ _ _ (fun y => y ∈ X)).
    Qed.
  End Diagonal.
End Diagonal.

Module Graph.
  Section Graph.
    Context `{Set_.Theory}.

    Theorem subset_of_product_essence (G : Graph) :
      ⊢ G ⊂ pr₁⟨G⟩ × pr₂⟨G⟩.
    Proof.
      Apply Graph.inclusionₑ.
      Rewrite CoupleMembershipEquivalenceProof.proof.
      Rewrite MembershipEquivalenceProof.proof.
      Intros x y H₁ [[] | []];
        Assumption.
    Qed.

    Theorem emptiness (G : Graph) :
      ⊢ is_empty pr₁⟨G⟩ ∨ is_empty pr₂⟨G⟩ ⇒ is_empty G.
    Proof.
      Rewrite Graph.subset_of_product_essence.
      Apply Product.emptinessₑ.
    Qed.
  End Graph.
End Graph.

Module Product.
  Section Product.
    Context `{Set_.Theory}.

    Theorem reverseₑ :
      ⊢ ∀ X Y, (X × Y)⁻¹ = Y × X.
    Proof.
      Rewrite Graph.equalityₑ.
      Intros X Y y x.
      do 2 (Rewrite CoupleMembershipEquivalenceProof.proof).
      Apply Conjunction.commutativity.
    Qed.
  End Product.
End Product.

Module Other.
  Section Other.
    Context `{Set_.Theory}.

    Lemma Rem_E_II_3__1 :
      ⊢ ¬has_graph (fun x y => x = y).
    Proof.
      Intros [G [contra₁ contra₂]].
      Apply Other.Rem_E_II_1__2.
      Intros [x].
      Rewrite (MembershipEquivalenceProof.proof pr₁⟨G⟩).
      Rewrite <- contra₂.
      Apply Equality.reflexivity.
    Qed.

    Lemma Pr_E_II_3__2 G :
      ⊢ ∀ X Y, X ⊂ Y ⇒ G⟨X⟩ ⊂ G⟨Y⟩.
    Proof.
      Intros X Y H₁.
      Rewrite H₁.
    Qed.
  End Other.
End Other.