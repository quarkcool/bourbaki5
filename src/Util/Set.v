Require Export
  Bourbaki.Root
  Bourbaki.Util.Notation.

Declare Scope bourbaki_meta_set_scope.
Delimit Scope bourbaki_meta_set_scope with mset.
#[local] Open Scope bourbaki_meta_set_scope.

Module Set_.
  Definition Set_ T := T -> Type.
  Bind Scope bourbaki_meta_set_scope with Set_.

  Definition empty_set {T} : Set_ T := fun _ => False.

  Definition membership {T} x (X : Set_ T) := X x.

  Infix "∈" := membership : type_scope.

  Definition non_membership {T} x (X : Set_ T) := x ∈ X -> False.

  Infix "∉" := non_membership : type_scope.

  Class DecidableMembership {T} (X : Set_ T) :=
  decidable_membership : forall x, ((x ∈ X) + (x ∉ X))%type.

  Definition difference {T} (X Y : Set_ T) :
    Set_ T :=
  fun x => ((x ∈ X) * (x ∉ Y))%type.

  #[local] Set Typeclasses Unique Instances.
  Class Inclusion {T} (X Y : Set_ T) := inclusion : forall x, x ∈ X -> x ∈ Y.

  Definition singleton {T} x : Set_ T := fun y => y = x.

  Definition union {T} (X Y : Set_ T) :
    Set_ T :=
  fun x => ((x ∈ X) + (x ∈ Y))%type.
End Set_.
Export (notations) Set_.
Export Set_ (Set_, DecidableMembership, Inclusion).

Notation "∅" := Set_.empty_set : bourbaki_meta_set_scope.

Infix "\" := Set_.difference : bourbaki_meta_set_scope.

Infix "⊂" := Inclusion : type_scope.

Notation "{ x , }" := (Set_.singleton x) : bourbaki_meta_set_scope.

Infix "∪" := Set_.union : bourbaki_meta_set_scope.