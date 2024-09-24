Require Export
  Bourbaki.Correspondence.Relation.Bijectivity.

Section Permutation.
  Context `{Formal.Theory, !Equality.Syntax, !Set_.Syntax}.

  Structure Permutation X := {
    function :> X → X;
    #[export, canonical=no] permutation_essence :: IsBijective function
  }.
End Permutation.