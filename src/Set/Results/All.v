Require Export
  Bourbaki.Logic.Results.All
  Bourbaki.Set.Results.Meta.Inclusion.

Module Other.
  Section Other.
    Context `{Quantification.Theory, !Equality.Syntax, !Set_.Syntax}.

    Lemma Pr_E_II_1__2 :
      ⊢ ∀ x y z, x ⊂ y ∧ y ⊂ z ⇒ x ⊂ z.
    Proof.
      Rewrite Conjunction.as_conditionₑ.
      Apply Inclusion.transitivity.
    Qed.
  End Other.
End Other.