Require Export
  Bourbaki.Correspondence.Correspondence.CanonicalSection
  Bourbaki.Correspondence.Relation.SectionEssence
  Bourbaki.Correspondence.Results.FunctionComposite.

Section CanonicalSection.
  Context `{Set_.Theory}.

  (* Pr_E_II_3__8_iii *)
  Theorem section_essence {X Y} (f : X → Y) `(!IsSurjective f) :
    ⊢ is_section (canonical_section f) f.
  Proof.
    Apply Application.equality_when_same_domainₑ.
    Intros y H₁.
    do 2 (Rewrite ValueEqualityProof.proof).
    Apply Conjunction.elimination_right.
    Rewrite <- (Existence.definition (fun x => _ ∧ f x = y)).
    Rewrite Equality.commutativity.
    Apply (MembershipEquivalenceProof.proof f⟨X⟩).
    Rewrite Surjectivity.surjectivity.
    Assumption.
  Qed.
End CanonicalSection.