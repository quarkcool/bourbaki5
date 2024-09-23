Require Export
  Bourbaki.Correspondence.Results.Meta.GraphPossession
  Bourbaki.Correspondence.Results.Meta.GraphProjections
  Bourbaki.Correspondence.Results.Meta.Product
  Bourbaki.Correspondence.Results.Meta.RelationGraph
  Bourbaki.Correspondence.Term.Application.

Section TermFunction.
  Context `{Set_.Theory}.

  (* C54_i *)
  #[export]
  Instance :
    forall X 𝐓, HasGraph (fun x y => x ∈ X ∧ y = 𝐓 x).
  Proof.
    Intros X 𝐓.
    Apply GraphPossession.from_container_set.
    Intros [x y H₁].
    Apply (
      CoupleMembershipEquivalenceProof.proof (X × set_by_replacement 𝐓 X)
    ).
    Rewrite MembershipEquivalenceProof.proof.
    Intros [| [[|]]];
      Assumption.
  Qed.

  (* C54_iii *)
  Theorem first_projectionₑ 𝐓 :
    ⊢ ∀ X, pr₁⟨{❨x, y❩ | x ∈ X ∧ y = 𝐓 x}⟩ = X.
  Proof.
    Rewrite Set_.equalityₑ.
    Intros X x.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite (Conjunction.commutativity (_ ∈ _)).
    Apply Existence.of_equalₑ.
  Qed.

  (* C54_iv *)
  Theorem second_projectionₑ 𝐓 :
    ⊢ ∀ X, pr₂⟨{❨x, y❩ | x ∈ X ∧ y = 𝐓 x}⟩ = set_by_replacement 𝐓 X.
  Proof.
    Rewrite Set_.equalityₑ.
    Intros X y.
    Rewrite MembershipEquivalenceProof.proof.
    Rewrite CoupleMembershipEquivalenceProof.proof.
    Rewrite (fun _ => Conjunction.commutativity (_ ∈ _)).
  Qed.

  #[export]
  Instance :
    forall {X Y} 𝐓 `(!set_by_replacement 𝐓 X ⊢⊂ Y),
      IsCorrespondence {❨x, y❩ | x ∈ X ∧ y = 𝐓 x} X Y.
  Proof.
    Intros X Y 𝐓 H₁ [|].
    { Rewrite TermFunction.first_projectionₑ. }
    { Rewrite TermFunction.second_projectionₑ.
      Assumption. }
  Qed.

  (* C54_ii *)
  #[export]
  Instance :
    forall {X Y} 𝐓 `(!set_by_replacement 𝐓 X ⊢⊂ Y),
      IsFunction {❨x, y❩ | x ∈ X ∧ y = 𝐓 x} X Y.
  Proof.
    Intros X Y 𝐓 H₁ [| [x y₁ y₂ |]].
    { Rewrite CoupleMembershipEquivalenceProof.proof.
      Intros H₂ H₃.
      Rewrite H₂.
      Rewrite H₃. }
    { Rewrite TermFunction.first_projectionₑ. }
  Qed.

  Definition term_function {X Y} 𝐓 `(!set_by_replacement 𝐓 X ⊢⊂ Y) :
    X → Y :=
  {❨x, y❩ | x ∈ X ∧ y = 𝐓 x}.
End TermFunction.

Notation "x ∈ X ↦ 𝐓" :=
  (
    term_function
      (X := X)
      (Y := set_by_replacement (fun x => 𝐓) X)
      (fun x => 𝐓)
      _
  ) :
bourbaki_scope.

Notation "x ∈ X ↦ 𝐓 ∈ Y" :=
  (term_function (X := X) (Y := Y) (fun x => 𝐓) _) :
bourbaki_scope.