module

public import STC.Control.Recovery

/-!
# Recovery-lane evidence
-/

namespace STC.Examples.GlobalRecovery

open STC STC.Control

@[expose] public section

def step (_label before after : Nat) : Prop := after = before

def profile : RecoveryProfile Nat Nat step where
  inverse := fun x y => x = y
  continuationStable := fun x y => x = y
  landingCoherent := fun x y => x = y
  cleanup := fun x y => x = y
  inverse_step := by
    intro label before after h
    exact h

theorem inverse_profile {label before after} (h : step label before after) :
    profile.inverse after before :=
  recovery_profile_inverse profile h

end

end STC.Examples.GlobalRecovery
