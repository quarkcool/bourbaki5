Require Export
  Bourbaki.Formal.Model.Syntax.

Section LetterSquareSubstitution.
  Context `{𝒯Syn : TheorySyntax}.

  Fixpoint substitute_letter_with_square_in_term
    n_let n_sq x :=
  match x with
  | square _ =>
    x
  | letter n =>
    if n == n_let then square n_sq else x
  | tau 𝐑 =>
    tau (substitute_letter_with_square_in_relation n_let (S n_sq) 𝐑)
  end

  with substitute_letter_with_square_in_term_list
    {n} n_let n_sq (xs : TermList n) :=
  match xs with
  | nil =>
    nil
  | cons x xs =>
    cons
      (substitute_letter_with_square_in_term n_let n_sq x)
      (substitute_letter_with_square_in_term_list n_let n_sq xs)
  end

  with substitute_letter_with_square_in_relation
    n_let n_sq 𝐀 :=
  match 𝐀 with
  | negation 𝐀 =>
    negation (substitute_letter_with_square_in_relation n_let n_sq 𝐀)
  | disjunction 𝐀 𝐁 =>
    disjunction
      (substitute_letter_with_square_in_relation n_let n_sq 𝐀)
      (substitute_letter_with_square_in_relation n_let n_sq 𝐁)
  | specific_relation sgn xs =>
    specific_relation
      sgn
      (substitute_letter_with_square_in_term_list n_let n_sq xs)
  end.
End LetterSquareSubstitution.