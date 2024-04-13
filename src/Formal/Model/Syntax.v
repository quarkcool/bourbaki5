Require Export
  Bourbaki.Formal.Model.TheorySyntax.

Section Syntax.
  Context `{𝒯Syn : TheorySyntax}.

  (* terme *)
  Inductive Term :=
  | square :
    nat -> Term
  (* lettre *)
  | letter :
    nat -> Term
  | tau :
    Relation -> Term

  with TermList : nat -> Type :=
  | nil :
    TermList 0
  | cons :
    forall {n}, Term -> TermList n -> TermList (S n)

  (* relation *)
  with Relation :=
  | negation :
    Relation -> Relation
  | disjunction :
    Relation -> Relation -> Relation
  | specific_relation :
    forall sgn, TermList (specific_sign_weight sgn) -> Relation.
End Syntax.