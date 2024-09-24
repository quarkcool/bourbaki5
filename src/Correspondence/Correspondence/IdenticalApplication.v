Require Export
  Bourbaki.Correspondence.Correspondence.CanonicalApplication.

Section IdenticalApplication.
  Context `{Set_.Theory}.

  (* application identique *)
  Definition identical_application X : X → X := canonical_application _.
End IdenticalApplication.

Notation Id := identical_application.