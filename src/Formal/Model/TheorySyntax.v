Require Export
  Bourbaki.Root
  Coq.Classes.EquivDec.

(* théorie *)
Class TheorySyntax := {
  (* signe spécifique *)
  SpecificSign : Type;
  SpecificSign_decidable_equality :: EqDec SpecificSign eq;

  (* poids d'un signe spécifique *)
  specific_sign_weight : SpecificSign -> nat
}.

Arguments SpecificSign {𝒯Syn} : rename.
Arguments specific_sign_weight {𝒯Syn} : rename.