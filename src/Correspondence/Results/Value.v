Require Export
  Bourbaki.Correspondence.Results.FunctionEssence
  Bourbaki.Correspondence.Term.Value.

Section Value.
  Context `{Set_.Theory}.

  #[export]
  Instance :
    forall {X Y} (x : Element X) (f : X → Y),
      IsFunctional (fun y => ❨x, y❩ ∈ f).
  Proof.
    Intros X Y x f.
    Apply FunctionEssence.alternative_definition.
    Apply Element.membership.
  Qed.

  Theorem as_equalₑ {X Y} (f : X → Y) (x : Element X) :
    ⊢ ∀ y, y = f x ⇔ ❨x, y❩ ∈ f.
  Proof.
    Intros y.
    Rewrite <- FunctionalEssence.common_term.
  Qed.

  Theorem value_essence {X Y} (f : X → Y) (x : Element X) :
    ⊢ ❨x, f x❩ ∈ f.
  Proof.
    Apply Value.as_equalₑ.
    Reflexivity.
  Qed.

  Theorem element_essence {X Y} (f : X → Y) (x : Element X) :
    ⊢ f x ∈ pr₂⟨f⟩.
  Proof.
    Apply MembershipEquivalenceProof.proof.
    Apply Value.value_essence.
  Qed.
End Value.