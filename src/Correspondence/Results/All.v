Require Export
  Bourbaki.Correspondence.Results.Meta.Image
  Bourbaki.Correspondence.Results.Meta.Product
  Bourbaki.Set.Results.Meta.Emptiness.

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