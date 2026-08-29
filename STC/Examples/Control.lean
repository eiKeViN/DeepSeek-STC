module

public import STC.Control

/-!
# Finite control evidence

This fixture gives nonempty orchestration and lifecycle relations, indexed traces,
an explicit in-flight boundary, and finite positive/negative checks for the Control
API.
-/

namespace STC.Examples.Control

open STC.Control

@[expose] public section

section Fixture

abbrev State := ControlState Nat (List Nat) Nat Nat Unit Nat Bool Nat
abbrev OLabel := OrchestrationLabel Nat Unit
abbrev LLabel := LifecycleLabel Nat Nat Unit Nat Bool

def inactive : State :=
  { raw := 0, traceMeta := [], mode := .inactive, inFlight := none, outcome := none }

def inserted : State :=
  { inactive with traceMeta := [1] }

def reloading : State :=
  { inserted with
      mode := .reloading
      inFlight := some
        { owner := 1
          launch := inserted.raw
          committed := ()
          remaining := 1
          prefixUndo := 0
          landingWitness := { future := 7, admissible := fun _ => True } } }

def active : State := { reloading with mode := .active, inFlight := none }

def unloading : State := { active with mode := .unloading }

def terminal : State := { inactive with traceMeta := [1], outcome := some true }

def orchestration : OLabel → State → State → Prop
  | .insert fresh _, before, after =>
      fresh ∉ before.traceMeta ∧ after = { before with traceMeta := fresh :: before.traceMeta }
  | .retire owner, before, after => owner ∈ before.traceMeta ∧ before.mode = .active ∧ after = before
  | .remove owner, before, after => owner ∈ before.traceMeta ∧ before.mode = .inactive ∧ after = before

def lifecycle : LLabel → State → State → Prop
  | .begin owner _, before, after => owner ∈ before.traceMeta ∧ before.outcome = none ∧ before.mode = .inactive ∧ after = reloading
  | .iter owner _, before, after => owner ∈ before.traceMeta ∧ before.outcome = none ∧ before.mode = .reloading ∧ after = before
  | .finish owner, before, after => owner ∈ before.traceMeta ∧ before.outcome = none ∧ before.mode = .reloading ∧ after = active
  | .divert owner .land, before, after => owner ∈ before.traceMeta ∧ before.outcome = none ∧ before.mode = .reloading ∧ after = active
  | .divert owner .abort, before, after => owner ∈ before.traceMeta ∧ before.outcome = none ∧ before.mode = .reloading ∧ after = inserted
  | .raise owner failure, before, after => owner ∈ before.traceMeta ∧ before.outcome = none ∧ after = { before with outcome := some failure.error }
  | .leave owner, before, after => owner ∈ before.traceMeta ∧ before.outcome = none ∧ before.mode = .active ∧ after = unloading
  | .unload owner, before, after => owner ∈ before.traceMeta ∧ before.outcome = none ∧ before.mode = .unloading ∧ after = terminal

def model : ControlModel OLabel LLabel State where
  orchestration := orchestration
  lifecycle := lifecycle

theorem insert_step : orchestration (.insert 1 ()) inactive inserted := by
  exact ⟨by simp [inactive], by rfl⟩

theorem begin_step : lifecycle (.begin 1 ()) inserted reloading := by
  exact ⟨by simp [inserted, inactive], by rfl, by rfl, rfl⟩

theorem finish_step : lifecycle (.finish 1) reloading active := by
  exact ⟨by simp [reloading, inserted, inactive], by rfl, by rfl, rfl⟩

theorem leave_step : lifecycle (.leave 1) active unloading := by
  exact ⟨by simp [active, reloading, inserted, inactive], by rfl, by rfl, rfl⟩

theorem unload_step : lifecycle (.unload 1) unloading terminal := by
  exact ⟨by simp [unloading, active, reloading, inserted, inactive], by rfl, by rfl, rfl⟩

def reloadTrace : Trace orchestration lifecycle inserted active :=
  .cons (.lifecycle (.begin 1 ()) begin_step)
    (.cons (.lifecycle (.finish 1) finish_step) .nil)

def unloadTrace : Trace orchestration lifecycle active terminal :=
  .cons (.lifecycle (.leave 1) leave_step)
    (.cons (.lifecycle (.unload 1) unload_step) .nil)

theorem reloadTrace_length : reloadTrace.length = 2 := by decide

theorem reloadTrace_lifecycle_only : reloadTrace.onlyLifecycle := by
  simp [reloadTrace, Trace.onlyLifecycle]

theorem unloadTrace_maximal :
    MaximalLifecycleSuffix orchestration lifecycle unloadTrace := by
  constructor
  · simp [unloadTrace, Trace.onlyLifecycle]
  · intro h
    rcases h with ⟨label, next, hnext⟩
    cases label with
    | begin owner target => simp [lifecycle, terminal] at hnext
    | iter owner nextCode => simp [lifecycle, terminal] at hnext
    | finish owner => simp [lifecycle, terminal] at hnext
    | divert owner choice => cases choice <;> simp [lifecycle, terminal] at hnext
    | raise owner failure => simp [lifecycle, terminal] at hnext
    | leave owner => simp [lifecycle, terminal] at hnext
    | unload owner => simp [lifecycle, terminal] at hnext

theorem orchestration_trace_not_lifecycle_only :
    ¬ (Trace.cons (.orchestration (.insert 1 ()) insert_step) reloadTrace).onlyLifecycle := by
  exact orchestration_not_onlyLifecycle (.insert 1 ()) insert_step reloadTrace

end Fixture

section AsyncAndFailure

def asyncPolicy : AsyncPolicy Nat State where
  atBoundary := fun _ state => state.mode = .reloading
  landingWitness := fun _ _ => True
  allowed := fun _ state choice => choice = .land ∨ (choice = .abort ∧ state.mode = .reloading)
  mustLand := by
    intro flight state
    exact Or.inl rfl
  landSound := by
    intro flight state h
    trivial
  abortGuard := by
    intro flight state h
    rcases h with h | ⟨_, hmode⟩
    · simp at h
    · exact hmode

theorem allowed_landing : landingAllowed asyncPolicy 7 active .land := by
  exact Or.inl rfl

theorem mid_stage_abort_rejected : ¬ landingAllowed asyncPolicy 7 active .abort := by
  intro h
  rcases h with h | ⟨hchoice, hmode⟩
  · simp at h
  · simp at hchoice
    simp [active, reloading] at hmode

def failure : Failure Nat Bool :=
  { error := true, boundary := reloading.raw, prefixUndo := fun n => n - 1 }

theorem failure_label_preserves :
    raiseLabel (Q := Nat) (V := Unit) 1 (.failure failure : ExecResult Nat Bool) =
      some (.raise 1 failure) := by
  exact raiseLabel_failure_preserves 1 failure

theorem success_cannot_raise :
    raiseLabel (Q := Nat) (V := Unit) 1 (.success ⟨active.raw, id⟩ : ExecResult Nat Bool) = none := by
  exact raiseLabel_success_absent 1 ⟨active.raw, id⟩

end AsyncAndFailure

structure Report where
  traceLength : Nat
  lifecycleOnly : Bool
  maximalTerminal : Bool
  landingAllowed : Bool
  abortRejected : Bool
  failurePreserved : Bool

def report : Report :=
  { traceLength := 2
    lifecycleOnly := true
    maximalTerminal := true
    landingAllowed := true
    abortRejected := true
    failurePreserved := true }

def expectedReport : Report :=
  { traceLength := 2
    lifecycleOnly := true
    maximalTerminal := true
    landingAllowed := true
    abortRejected := true
    failurePreserved := true }

theorem report_eq_expected : report = expectedReport := by
  rfl

end

end STC.Examples.Control
