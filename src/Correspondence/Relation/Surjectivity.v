Require Export
  Bourbaki.Correspondence.Term.Application
  Bourbaki.Correspondence.Term.Image.

Section Surjectivity.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  (*
    Def_E_II_3__10_ii /
    f est une surjection /
    f est [une application] surjective /
    f est une application de X sur Y /
    f est une représentation paramétrique de Y au moyen de X
  *)
  Definition is_surjective {X Y} (f : X → Y) := f⟨X⟩ = Y.

  #[local] Set Typeclasses Unique Instances.
  Class IsSurjective {X Y} (f : X → Y) := surjectivity : ⊢ is_surjective f.
End Surjectivity.