module

public import STC.Control.Canonical

/-!
# Canonical/confluence evidence
-/

namespace STC.Examples.GlobalConfluence

open STC STC.Control

@[expose] public section

def envelope : ConfluenceEnvelope Nat Nat where
  canonical := fun _ => True
  admissible := fun _ => True
  nonfailed := fun _ => True
  sameInputs := fun _ _ => True
  sameWitnesses := fun _ _ => True
  alphaComplete := True

end

end STC.Examples.GlobalConfluence
