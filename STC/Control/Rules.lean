module

public import STC.Control
public import STC.State.Global

/-!
# Guarded global rule families

This module is the single authoritative relation for the repaired, old-paper
single-realm calculus. Orchestration allocates or removes names; lifecycle
steps only edit an existing positive cell.
-/

universe u v w x

namespace STC.Control

open STC STC.State

@[expose] public section

section Rules

variable {Name : Type u} {Key : Type v} {Value : Type w}
variable {Action : Type u} {Iterator : Type v} {Accumulator : Type w}
variable {Flight : Type u} {Failure : Type v} {Ambient : Type x}
variable [DecidableEq Name] [DecidableEq Key]

local notation "GState" =>
  GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient
local notation "GCell" => FiberCell Name Key Value Action Iterator Accumulator Flight Failure
local notation "GComponent" => Component Key Value Action Iterator Accumulator Flight Failure

inductive DivertChoice where
  | land
  | abort
  deriving DecidableEq, Repr

inductive GlobalOrchestrationLabel (Name : Type u) (Cell : Type v) where
  | insert (fresh : Name) (cell : Cell)
  | retire (owner : Name)
  | remove (owner : Name)
  

inductive GlobalLifecycleLabel (Name : Type u) (Failure : Type v) where
  | begin (owner : Name)
  | iter (owner : Name)
  | finish (owner : Name)
  | divert (owner : Name) (choice : DivertChoice)
  | raise (owner : Name) (failure : Failure)
  | leave (owner : Name)
  | unload (owner : Name)
  

local notation "OLabel" => GlobalOrchestrationLabel Name GCell
local notation "LLabel" => GlobalLifecycleLabel Name Failure

def insertState (state : GState) (fresh : Name) (cell : GCell) : GState :=
  { state with
      registry := Finmap.insert fresh cell state.registry
      ledger := { everIssued := insert fresh state.ledger.everIssued }
      allocationHistory := state.allocationHistory ++ [fresh] }

def editCell (state : GState) (owner : Name) (edit : GCell → GCell) : GState :=
  match Finmap.lookup owner state.registry with
  | none => state
  | some cell => updateFiber state owner (edit cell)

def retireState (state : GState) (owner : Name) : GState :=
  editCell state owner (fun cell => { cell with retired := true })

def removeState (state : GState) (owner : Name) : GState :=
  { state with registry := Finmap.erase owner state.registry }

def phaseState (state : GState) (owner : Name) (phase : LifecyclePhase) : GState :=
  editCell state owner (fun cell => { cell with phase := phase })

def failState (state : GState) (owner : Name) (failure : Failure) : GState :=
  editCell state owner (fun cell =>
    { cell with phase := .failed, payload := { cell.payload with failureData := some failure } })

def orchestrationRule (label : OLabel) (before after : GState) : Prop :=
  match label with
  | .insert fresh cell =>
      fresh ∉ before.registry.keys ∧ fresh ∉ before.ledger.everIssued ∧
        after = insertState before fresh cell
  | .retire owner =>
      (∃ cell, Finmap.lookup owner before.registry = some cell ∧ cell.phase = .active ∧
        after = retireState before owner)
  | .remove owner =>
      (∃ cell, Finmap.lookup owner before.registry = some cell ∧ cell.phase = .inactive ∧
        cell.retired = true ∧ after = removeState before owner)

def lifecycleRule (label : LLabel) (before after : GState) : Prop :=
  match label with
  | .begin owner =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧ cell.phase = .inactive ∧
        cell.retired = false ∧ after = phaseState before owner .reloading
  | .iter owner =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧ cell.phase = .reloading ∧
        after = phaseState before owner .reloading
  | .finish owner =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧ cell.phase = .reloading ∧
        cell.payload.failureData = none ∧ after = phaseState before owner .active
  | .divert owner .land =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧ cell.phase = .reloading ∧
        after = phaseState before owner .active
  | .divert owner .abort =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧ cell.phase = .reloading ∧
        after = phaseState before owner .inactive
  | .raise owner failure =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧ cell.phase = .reloading ∧
        after = failState before owner failure
  | .leave owner =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧ cell.phase = .active ∧
        after = phaseState before owner .unloading
  | .unload owner =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧ cell.phase = .unloading ∧
        cell.retired = true ∧ after = removeState before owner

/-- `R.full` is the union of the two typed relation classes. -/
def fullRule (label : Sum OLabel LLabel) (before after : GState) : Prop :=
  match label with
  | .inl orchestration => orchestrationRule orchestration before after
  | .inr lifecycle => lifecycleRule lifecycle before after

def globalControlModel : ControlModel OLabel LLabel GState where
  orchestration := orchestrationRule
  lifecycle := lifecycleRule

/-- Derived views of the authoritative relation. -/
def withdrawRule (label : OLabel) (before after : GState) : Prop :=
  match label with
  | .retire _ | .remove _ => orchestrationRule label before after
  | .insert _ _ => False

def iterationRule (label : LLabel) (before after : GState) : Prop :=
  match label with
  | .begin _ | .iter _ | .finish _ | .divert _ _ | .leave _ | .unload _ =>
      lifecycleRule label before after
  | .raise _ _ => False

def failureRule (label : LLabel) (before after : GState) : Prop :=
  match label with
  | .raise _ _ => lifecycleRule label before after
  | _ => False

theorem fullRule_inl (label : OLabel) (before after : GState) :
    fullRule (.inl label) before after ↔ orchestrationRule label before after := by rfl

theorem fullRule_inr (label : LLabel) (before after : GState) :
    fullRule (.inr label) before after ↔ lifecycleRule label before after := by rfl

theorem withdrawRule_subfamily (label : OLabel) (before after : GState)
    (h : withdrawRule label before after) : orchestrationRule label before after := by
  cases label <;> simp [withdrawRule] at h ⊢
  · exact h
  · exact h

theorem iterationRule_subfamily (label : LLabel) (before after : GState)
    (h : iterationRule label before after) : lifecycleRule label before after := by
  cases label <;> simp [iterationRule] at h ⊢
  all_goals exact h

theorem failureRule_subfamily (label : LLabel) (before after : GState)
    (h : failureRule label before after) : lifecycleRule label before after := by
  cases label <;> simp [failureRule] at h ⊢
  exact h

end Rules

end

end STC.Control
