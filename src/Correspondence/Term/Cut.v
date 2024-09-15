Require Export
  Bourbaki.Correspondence.Term.Image.

(* Def_E_II_3__4 / coupe de G suivant x *)
Definition cut `{Formal.Theory, !Equality.Syntax, !Set_.Syntax} G x := G⟨{x,}⟩.