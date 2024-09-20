Require Export
  Bourbaki.Correspondence.Term.Application
  Bourbaki.Set.Term.Element.

Section Value.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  (*
    Def_E_II_3__9_iii /
    valeur de f pour l'élément x de X /
    transformé de x par f /
    image de x par f
  *)
  Definition value {X Y} (f : X → Y) x := τ y, ❨x, y❩ ∈ f.
End Value.

Coercion value : Application >-> Funclass.