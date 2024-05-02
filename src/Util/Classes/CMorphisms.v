Require Export
  Bourbaki.Root
  Coq.Classes.CMorphisms
  Coq.Classes.RelationClasses.

Hint Mode CRelationClasses.Reflexive + + : typeclass_instances.

#[global] Remove Hints CMorphisms.Normalizes : typeclass_instances.
#[global] Remove Hints CMorphisms.Proper : typeclass_instances.
#[global] Remove Hints CMorphisms.ProperProxy : typeclass_instances.
#[global] Remove Hints CRelationClasses.Reflexive : typeclass_instances.
#[global] Remove Hints CRelationClasses.subrelation : typeclass_instances.

Set Universe Polymorphism.

Module Hijacking.
  Lemma eq_proper_proxy {T} x :
    CMorphisms.ProperProxy (@eq T) x.
  Proof.
    firstorder.
  Defined.

  Lemma flip1 {T R₁ R₂} `(CRelationClasses.subrelation T R₁ R₂) :
    CRelationClasses.subrelation
      (CRelationClasses.flip (CRelationClasses.flip R₁))
      R₁.
  Proof.
    firstorder.
  Defined.

  Lemma flip2 {T R₁ R₂} `(CRelationClasses.subrelation T R₁ R₂) :
    CRelationClasses.subrelation
      R₁
      (CRelationClasses.flip (CRelationClasses.flip R₂)).
  Proof.
    firstorder.
  Defined.

  Lemma flip_arrow
    {T₁ R₁ R₂ T₂ R₃ R₄}
    `(
      H₁ : CMorphisms.Normalizes T₁ R₁ (CRelationClasses.flip R₂),
      H₂ : CMorphisms.Normalizes T₂ R₃ (CRelationClasses.flip R₄)
    ) :
      CMorphisms.Normalizes
        (T₁ -> T₂)
        (R₁ ==> R₃)%signatureT
        (CRelationClasses.flip (R₂ ==> R₄)%signatureT).
  Proof.
    unfold Normalizes in *.
    intros f g.
    split;
      intros H₃ x y H₄;
      apply H₂;
      apply H₃;
      apply H₁;
      assumption.
  Defined.

  Lemma flip_atom {T} R :
    CMorphisms.Normalizes T R (CRelationClasses.flip (CRelationClasses.flip R)).
  Proof.
    firstorder.
  Defined.

  Lemma flip_Reflexive {T R} `{CRelationClasses.Reflexive T R} :
    CRelationClasses.Reflexive (CRelationClasses.flip R).
  Proof.
    tauto.
  Defined.

  Lemma proper_normalizes_proper
    {T R₁ R₂ f} `(CMorphisms.Normalizes _ R₁ R₂, CMorphisms.Proper T R₂ f) :
      CMorphisms.Proper R₁ f.
  Proof.
    apply (_ : CMorphisms.Normalizes _ R₁ R₂).
    assumption.
  Defined.

  Lemma Reflexive_partial_app_morphism
    {T₁ T₂ R₁ R₂ f x}
    `(
      CMorphisms.Proper (T₁ -> T₂) (R₁ ==> R₂) f,
      CMorphisms.ProperProxy T₁ R₁ x
    ) :
      Proper R₂ (f x).
  Proof.
    simpl_crelation.
  Defined.

  Lemma reflexive_proper_proxy {T R} `(CRelationClasses.Reflexive T R) x :
    ProperProxy R x.
  Proof.
    firstorder.
  Defined.

  Lemma subrelation_proper
    {T R₁ f R₂}
    `(mor : CMorphisms.Proper T R₁ f)
    `(Unconvertible (CRelationClasses.crelation T) R₂ R₁)
    `(sub : CRelationClasses.subrelation T R₁ R₂) :
      CMorphisms.Proper R₂ f.
  Proof.
    intros.
    apply sub.
    apply mor.
  Defined.

  Lemma subrelation_refl {T} R :
    @CRelationClasses.subrelation T R R.
  Proof.
    simpl_crelation.
  Defined.

  Lemma subrelation_respectful
    {T₁ R₁ R₂ T₂ R₃ R₄}
    `(
      CRelationClasses.subrelation T₁ R₁ R₂,
      CRelationClasses.subrelation T₂ R₃ R₄
    ) :
      CRelationClasses.subrelation
        (R₂ ==> R₃)%signatureT
        (R₁ ==> R₄)%signatureT.
  Proof.
    simpl_crelation.
  Defined.

  (*Program Instance trans_contra_inv_impl_type_morphism
    {T R} `(CRelationClasses.Transitive T R) x :
      Proper (R --> flip arrow) (R x) | 3.
  Next Obligation.
    intros z y H₁ H₂.
    eapply CRelationClasses.transitivity;
      eassumption.
  Defined.*)

  Ltac normalizes :=
  match goal with
  | [|- CMorphisms.Normalizes _ (CMorphisms.respectful _ _) _ ] =>
    class_apply @Hijacking.flip_arrow
  | _ =>
    class_apply @Hijacking.flip_atom
  end.

  Ltac partial_application_tactic :=
  let rec do_partial_apps H m cont :=
    match m with
    | ?m' ?x =>
      class_apply @Hijacking.Reflexive_partial_app_morphism;
      [(do_partial_apps H m' ltac:(idtac)) | clear H]
    | _ =>
      cont
    end
  in
  let rec do_partial H ar m :=
    match ar with
    | 0%nat =>
      do_partial_apps H m ltac:(fail 1)
    | S ?n' =>
      match m with
      | ?m' ?x => do_partial H n' m'
      end
    end
  in
  let params m sk fk :=
    (
      let m' := fresh in head_of_constr m' m;
      let n := fresh in evar (n:nat);
      let v := eval compute in n in clear n;
      let H := fresh in
      assert(H : CMorphisms.Params m' v) by typeclasses eauto;
      let v' := eval compute in v in subst m';
      (sk H v' || fail 1)
    ) || fk
  in
  let on_morphism m cont :=
    params m ltac:(fun H n => do_partial H n m) ltac:(cont)
  in
  match goal with
  | [_ : @CMorphisms.normalization_done |- _] =>
    fail 1
  | [_ : @CMorphisms.Params _ _ _ |- _] =>
    fail 1
  | [|- @CMorphisms.Proper ?T _ (?m ?x)] =>
    match goal with
      | [H : PartialApplication |- _] =>
        class_apply @Hijacking.Reflexive_partial_app_morphism;
        [|clear H]
      | _ => on_morphism (m x)
        ltac:(class_apply @Hijacking.Reflexive_partial_app_morphism)
    end
  end.

  Ltac proper_normalization :=
  match goal with
  | [ _ : @CMorphisms.normalization_done |- _ ] =>
    fail 1
  | [ _ : @CMorphisms.apply_subrelation |- @Proper _ ?R _ ] =>
    let H := fresh "H" in
    set(H:=@CMorphisms.did_normalization);
    class_apply @Hijacking.proper_normalizes_proper
  end.

  Ltac proper_subrelation :=
  match goal with
  | [H : apply_subrelation |- _] =>
    clear H;
    class_apply @Hijacking.subrelation_proper
  end.

  Ltac subrelation_tac T U :=
  (is_ground T ; is_ground U ; class_apply @Hijacking.subrelation_refl) ||
    class_apply @Hijacking.subrelation_respectful ||
      class_apply @Hijacking.subrelation_refl.
End Hijacking.
Export (hints) Hijacking.

Instance :
  forall T₁ {T₂} {R : CRelationClasses.crelation T₂},
    CRelationClasses.Reflexive R ->
      CRelationClasses.Reflexive (CMorphisms.pointwise_relation T₁ R).
Proof.
  intros T₁ T₂ R H₁ f x.
  reflexivity.
Defined.

Instance :
  forall {T₁ T₂} (R : T₁ -> CRelationClasses.crelation T₂),
    CRelationClasses.subrelation
      (CRelationClasses.flip
        (CMorphisms.forall_relation (fun x => CRelationClasses.flip (R x))))
      (CMorphisms.forall_relation (fun x => R x)).
Proof.
  intros T₁ T₂ R f g H₁ x.
  apply H₁.
Defined.

Instance :
  forall T₁ {T₂} (R : CRelationClasses.crelation T₂),
    CRelationClasses.subrelation
      (CRelationClasses.flip
        (CMorphisms.pointwise_relation T₁ (CRelationClasses.flip R)))
      (CMorphisms.pointwise_relation _ R).
Proof.
  intros T₁ T₂ R f g H₁ x.
  apply H₁.
Defined.

Definition forall_relation_Symmetric :
  forall {T₁ T₂} {R : T₁ -> CRelationClasses.crelation T₂},
    (forall x, CRelationClasses.Symmetric (R x)) ->
      CRelationClasses.Symmetric (CMorphisms.forall_relation (fun x => R x)).
Proof.
  intros T₁ T₂ R H₁ f g H₂ x.
  apply H₁.
  apply H₂.
Defined.

Instance :
  forall T₁ {T₂} {R : CRelationClasses.crelation T₂},
    CRelationClasses.Symmetric R ->
      CRelationClasses.Symmetric (CMorphisms.pointwise_relation T₁ R).
Proof.
  intros T₁ T₂ R H₁ f g H₂ x.
  apply H₁.
  apply H₂.
Defined.

Hint Extern 1 (CMorphisms.Normalizes _ _ _) =>
  Hijacking.normalizes :
typeclass_instances.

Hint Extern 2 (@CMorphisms.Proper _ (flip _) _) =>
  class_apply @CMorphisms.proper_flip_proper :
typeclass_instances.

Hint Extern 4 (@CMorphisms.Proper _ _ _) =>
  Hijacking.partial_application_tactic :
typeclass_instances.

Hint Extern 5 (@CMorphisms.Proper _ _ _) =>
  Hijacking.proper_subrelation :
typeclass_instances.

Hint Extern 6 (@CMorphisms.Proper _ _ _) =>
  Hijacking.proper_normalization :
typeclass_instances.

Hint Extern 1 (CMorphisms.ProperProxy _ _) =>
  class_apply @Hijacking.eq_proper_proxy ||
    class_apply @Hijacking.reflexive_proper_proxy :
typeclass_instances.

Hint Extern 3 (CRelationClasses.Reflexive (CRelationClasses.flip _)) =>
  apply Hijacking.flip_Reflexive :
typeclass_instances.

Hint Extern 1 (CRelationClasses.subrelation (CRelationClasses.flip _) _) =>
  class_apply @Hijacking.flip1 :
typeclass_instances.

Hint Extern 1 (CRelationClasses.subrelation _ (CRelationClasses.flip _)) =>
  class_apply @Hijacking.flip2 :
typeclass_instances.

Hint Extern 3 (@CRelationClasses.subrelation _ ?T ?U) =>
  Hijacking.subrelation_tac T U :
typeclass_instances.

Hint Extern 0 (CRelationClasses.Symmetric (CMorphisms.forall_relation _)) =>
  notypeclasses refine (forall_relation_Symmetric (fun _ => _)) :
typeclass_instances.