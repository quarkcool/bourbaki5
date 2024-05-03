Require Export
  Bourbaki.Logic.CoreTheory.

Module Logic.
  Class Theory `{Logic.CoreTheory} := {
    implication_introduction :
      forall 𝐀 𝐁, (⊢ 𝐀 -> ⊢ 𝐁) -> ⊢ 𝐀 ⇒ 𝐁
  }.
End Logic.