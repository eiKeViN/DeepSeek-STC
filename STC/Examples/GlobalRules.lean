module

public import STC.Control.Rules
public import STC.Examples.GlobalModel

/-!
# Global rule witnesses

The finite fixture inhabits all printed orchestration and lifecycle cases while
retaining explicit failure and both diversion branches.
-/

namespace STC.Examples.GlobalRules

open STC STC.State STC.Control

@[expose] public section

abbrev Cell := FiberCell Nat Nat Nat Unit Unit Unit Unit Unit
abbrev State := GlobalState Nat Nat Nat Unit Unit Unit Unit Unit Unit
abbrev OLabel := GlobalOrchestrationLabel Nat Cell
abbrev LLabel := GlobalLifecycleLabel Nat Unit

def component : Component Nat Nat Unit Unit Unit Unit Unit :=
  { key := 0, requires := ∅, provides := {0}, actionCode := (), iteratorCode := (),
    accumulatorCode := (), flightCode := (), failureCode := () }

def cell0 : Cell :=
  { incarnation := 0, parent := none, birth := 0, component := component,
    committed := { entries := ∅ }, committedView := ∅, retired := false, phase := .inactive,
    payload :=
      { iteratorCode := (), accumulatorCode := (), flightCode := none, failureData := none } }

def state0 : State :=
  { ambient := (), registry := ∅, coeffects := ∅,
    ledger := { everIssued := ∅ }, allocationHistory := [] }

def state1 : State := insertState state0 0 cell0

def stateReloading : State := phaseState state1 0 .reloading

def stateActive : State := phaseState stateReloading 0 .active

def stateRetired : State := retireState stateActive 0

def stateUnloading : State := phaseState stateRetired 0 .unloading

def retiredInactiveCell : Cell := { cell0 with retired := true }

def retiredInactiveState : State := insertState state0 0 retiredInactiveCell

/-- One value of every constructor in the authoritative labelled rule surface. -/
def labels : List (Sum OLabel LLabel) :=
  [ .inl (.insert 0 cell0)
  , .inl (.retire 0)
  , .inl (.remove 0)
  , .inr (.begin 0)
  , .inr (.iter 0)
  , .inr (.finish 0)
  , .inr (.divert 0 .land)
  , .inr (.divert 0 .abort)
  , .inr (.raise 0 ())
  , .inr (.leave 0)
  , .inr (.unload 0) ]

theorem state1_history : state1.allocationHistory = [0] := rfl

theorem labels_length : labels.length = 11 := rfl

theorem insert_rule : orchestrationRule (.insert 0 cell0) state0 state1 := by
  simp [orchestrationRule, state0, state1, insertState]

theorem begin_rule : lifecycleRule (.begin 0) state1 stateReloading := by
  refine ⟨cell0, ?_, rfl, rfl, rfl⟩
  simp [state0, state1, insertState]

theorem iter_rule : lifecycleRule (.iter 0) stateReloading
    (phaseState stateReloading 0 .reloading) := by
  refine ⟨{ cell0 with phase := .reloading }, ?_, rfl, rfl⟩
  simp [stateReloading, state1, state0, phaseState, editCell, insertState, updateFiber]

theorem finish_rule : lifecycleRule (.finish 0) stateReloading stateActive := by
  refine ⟨{ cell0 with phase := .reloading }, ?_, rfl, rfl, rfl⟩
  simp [stateReloading, state1, state0, phaseState, editCell, insertState, updateFiber]

theorem divert_land_rule : lifecycleRule (.divert 0 .land) stateReloading stateActive := by
  refine ⟨{ cell0 with phase := .reloading }, ?_, rfl, rfl⟩
  simp [stateReloading, state1, state0, phaseState, editCell, insertState, updateFiber]

theorem divert_abort_rule : lifecycleRule (.divert 0 .abort) stateReloading
    (phaseState stateReloading 0 .inactive) := by
  refine ⟨{ cell0 with phase := .reloading }, ?_, rfl, rfl⟩
  simp [stateReloading, state1, state0, phaseState, editCell, insertState, updateFiber]

theorem raise_rule :
    lifecycleRule (.raise 0 ()) stateReloading (failState stateReloading 0 ()) := by
  refine ⟨{ cell0 with phase := .reloading }, ?_, rfl, rfl⟩
  simp [stateReloading, state1, state0, phaseState, editCell, insertState, updateFiber]

theorem retire_rule : orchestrationRule (.retire 0) stateActive stateRetired := by
  refine ⟨{ cell0 with phase := .active }, ?_, rfl, rfl⟩
  simp [stateActive, stateReloading, state1, state0, phaseState, editCell, insertState,
    updateFiber]

theorem leave_rule : lifecycleRule (.leave 0) stateRetired stateUnloading := by
  refine ⟨{ cell0 with phase := .active, retired := true }, ?_, rfl, rfl⟩
  simp [stateRetired, stateActive, stateReloading, state1, state0, retireState, phaseState,
    editCell, insertState, updateFiber]

theorem unload_rule : lifecycleRule (.unload 0) stateUnloading (removeState stateUnloading 0) := by
  refine ⟨{ cell0 with phase := .unloading, retired := true }, ?_, rfl, rfl, rfl⟩
  simp [stateUnloading, stateRetired, stateActive, stateReloading, state1, state0, retireState,
    phaseState, editCell, insertState, updateFiber]

theorem remove_rule : orchestrationRule (.remove 0) retiredInactiveState
    (removeState retiredInactiveState 0) := by
  refine ⟨retiredInactiveCell, ?_, rfl, rfl, rfl⟩
  simp [retiredInactiveState, retiredInactiveCell, state0, insertState]

end

end STC.Examples.GlobalRules
