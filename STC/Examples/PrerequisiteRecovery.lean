module

public import STC.Core.Effect.Closure
public import STC.Core.Partial.Recovery

/-!
# Recovery prerequisite evidence

Finite declarations exercise generator membership and explicit recovery
contracts. They do not claim lifecycle continuation stability.
-/

namespace STC.Examples.PrerequisiteRecovery

open STC

@[expose] public section

def increment : Transformation Nat := { forward := fun n => n + 1, undo := fun n => n - 1 }
def decrement : Transformation Nat := { forward := fun n => n - 1, undo := fun n => n + 1 }

def generators : Transformation Nat → Prop := fun t => t = increment ∨ t = decrement

theorem increment_generated : Generated generators increment :=
  Generated.generator (Or.inl rfl)

theorem identity_generated : Generated generators Transformation.identity := Generated.identity

def recoveryOp : PartialOp Nat Unit := fun n => some { state := n + 1, undo := fun m => m - 1, outcome := () }

theorem recoveryOp_recovers : OperationRecovers (equality Nat) recoveryOp := by
  intro input result h
  simp [recoveryOp] at h
  subst result
  rfl

def recoverySpec : RecoverySpec (equality Nat) (fun _ _ : Unit => True) where
  op := recoveryOp
  respects := by
    intro x y h
    cases h
    simp [recoveryOp, OptionRel, OpResultRel]
    constructor
    · rfl
    · intro n
      rfl
  inverseStable := by
    intro input result h
    simp [recoveryOp] at h
    subst result
    intro x y hxy
    cases hxy
    rfl
  recovers := recoveryOp_recovers

theorem recovery_checked (n : Nat) :
    ∃ result, recoverySpec.op n = some result ∧
      result.undo result.state = n := by
  refine ⟨{ state := n + 1, undo := fun m => m - 1, outcome := () }, ?_, ?_⟩
  · rfl
  · simp

end

end STC.Examples.PrerequisiteRecovery
