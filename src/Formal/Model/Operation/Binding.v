Require Export
  Bourbaki.Formal.Model.Operation.FreshLetterRetrieval
  Bourbaki.Formal.Model.Operation.LetterSquareSubstitution.

Definition bind `{𝒯Syn : TheorySyntax} f :=
let n_let := get_fresh_letter_in_relation (f (square 0)) in
substitute_letter_with_square_in_relation n_let 0 (f (letter n_let)).