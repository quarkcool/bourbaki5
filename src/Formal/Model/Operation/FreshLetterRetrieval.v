Require Export
  Bourbaki.Formal.Model.Syntax.

Section FreshLetterRetrieval.
  Context `{𝒯Syn : TheorySyntax}.

  Fixpoint get_fresh_letter_in_term x :=
  match x with
  | square _ =>
    0
  | letter n =>
    S n
  | tau 𝐑 =>
    get_fresh_letter_in_relation 𝐑
  end

  with get_fresh_letter_in_term_list {n} (xs : TermList n) :=
  match xs with
  | nil =>
    0
  | cons x xs =>
    max (get_fresh_letter_in_term x) (get_fresh_letter_in_term_list xs)
  end

  with get_fresh_letter_in_relation 𝐀 :=
  match 𝐀 with
  | negation 𝐀 =>
    get_fresh_letter_in_relation 𝐀
  | disjunction 𝐀 𝐁 =>
    max (get_fresh_letter_in_relation 𝐀) (get_fresh_letter_in_relation 𝐁)
  | specific_relation _ xs =>
    get_fresh_letter_in_term_list xs
  end.
End FreshLetterRetrieval.