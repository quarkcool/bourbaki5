Require Export
  Bourbaki.Formal.Model.Theory
  Bourbaki.Formal.Relation.Implication.

(* démonstration *)
Inductive Proof `(𝒯 : Theory) : Relation -> Type :=
| explicit_axiom :
  forall 𝐀, 𝐀 ∈ 𝒯.(ExplicitAxioms) -> Proof 𝒯 𝐀
| implicit_axiom :
  forall 𝐀, 𝐀 ∈ 𝒯.(Schemas) -> Proof 𝒯 𝐀
(* syllogisme / C1 *)
| syllogism :
  forall 𝐀 𝐁, Proof 𝒯 𝐀 -> Proof 𝒯 (𝐀 ⇒ 𝐁) -> Proof 𝒯 𝐁.

Arguments explicit_axiom {_ _ _}.
Arguments implicit_axiom {_ _ _}.
Arguments syllogism {_ _ _ _}.

Infix "⊢" := Proof : type_scope.