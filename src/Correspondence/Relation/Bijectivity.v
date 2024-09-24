Require Export
  Bourbaki.Correspondence.Relation.Injectivity
  Bourbaki.Correspondence.Relation.Surjectivity.

Section Bijectivity.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  (*
    Def_E_II_3__10_iii /
    f est une bijection /
    f est [une application] bijective /
    f met X et Y en correspondance biunivoque
  *)
  Definition is_bijective {X Y} (f : X → Y) := is_injective f ∧ is_surjective f.

  #[local] Set Typeclasses Unique Instances.
  Class IsBijective {X Y} (f : X → Y) := bijectivity : ⊢ is_bijective f.
End Bijectivity.