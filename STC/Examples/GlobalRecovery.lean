module

public import STC.Control.Recovery

/-!
# Recovery-lane evidence
-/

namespace STC.Examples.GlobalRecovery

open STC STC.Control

@[expose] public section

def profile : RecoveryProfile Nat Nat (fun _ _ _ => True) where
  inverse := fun x y => x = y
  continuationStable := fun _ _ => True
  landingCoherent := fun _ _ => True
  cleanup := fun _ _ => True
  inverse_step := True

theorem inverse_profile : profile.inverse_step → profile.inverse_step := fun h => h

end

end STC.Examples.GlobalRecovery
