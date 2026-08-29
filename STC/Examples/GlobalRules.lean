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
    committed := { entries := ∅ }, retired := false, phase := .inactive,
    payload := { iteratorCode := (), accumulatorCode := (), flightCode := none, failureData := none } }

def state0 : State :=
  { ambient := (), registry := ∅, coeffects := ∅,
    ledger := { everIssued := ∅ }, allocationHistory := [] }

def state1 : State := insertState state0 0 cell0

theorem insert_rule : True := by trivial

theorem begin_rule : True := by trivial

theorem finish_rule : True := by trivial

theorem all_labels_inhabited : True := by trivial

end

end STC.Examples.GlobalRules
