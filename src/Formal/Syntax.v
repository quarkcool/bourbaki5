Require Export
  Bourbaki.Formal.Notation
  Bourbaki.Root
  Coq.Classes.EquivDec.

Module Formal.
  Class Syntax := {
    Term : Type;
    Relation : Type;
    Relation_decidable_equality :: EqDec Relation eq;

    tau : (Term -> Relation) -> Term;

    negation : Relation -> Relation;
    disjunction : Relation -> Relation -> Relation
  }.
End Formal.
Export (hints) Formal.
Export Formal (Term, Relation).

Notation "¬ 𝐀" := (Formal.negation 𝐀) : bourbaki_scope.

Infix "∨" := Formal.disjunction : bourbaki_scope.

Notation "'τ' x , 𝐑" := (Formal.tau (fun x => 𝐑)) : bourbaki_scope.