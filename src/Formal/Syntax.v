Require Export
  Bourbaki.Formal.Notation.

Module Formal.
  Class Syntax := {
    (* relation *)
    Relation : Type;
    (* terme *)
    Term : Type;

    (* négation *)
    negation : Relation -> Relation;
    (* disjonction *)
    disjunction : Relation -> Relation -> Relation;

    tau_abstraction : (Term -> Relation) -> Term
  }.
End Formal.
Export Formal (negation, disjunction, tau_abstraction).

Notation "¬ 𝐑" := (negation 𝐑) : bourbaki_scope.

Infix "∨" := disjunction : bourbaki_scope.

Notation "'τ' x , 𝐑" := (tau_abstraction (fun x => 𝐑)) : bourbaki_scope.