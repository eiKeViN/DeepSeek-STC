module

public import STC.State.Global.Observation

/-!
# Positive global-model evidence

This fixture only checks the data-only global carrier and its ordered allocation
history; semantic rule reachability remains a later lane.
-/

namespace STC.Examples.GlobalModel

open STC STC.State

@[expose] public section

abbrev Cell := FiberCell Nat Nat Nat Unit Unit Unit Unit Unit
abbrev State := GlobalState Nat Nat Nat Unit Unit Unit Unit Unit Unit

def empty : State :=
  { ambient := (), registry := ∅, coeffects := ∅,
    ledger := { everIssued := ∅ }, allocationHistory := [] }

theorem empty_history : empty.allocationHistory = [] := rfl
theorem empty_active : activeNames empty = ∅ := by
  classical
  rfl

end

end STC.Examples.GlobalModel
