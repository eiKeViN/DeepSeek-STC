/-
  ADR-07 compiler spike: control, nondeterminism, asynchrony, and failure.

  The spike is intentionally standalone and uses the namespace STCADR07.
  It does not redeclare or import production STC modules.  The production
  implementation will instantiate these interfaces with the P3/P4/P5
  Failure, ExecResult, iterator, and state declarations.

  The carrier has two labelled relation classes:
    * orchestration: an external input;
    * lifecycle: an internal state-enabled step.
  A finite indexed trace stores the selected class and its local premise.
  InFlight makes an asynchronous landing snapshot explicit, and the
  failure bridge preserves error, boundary, and prefixUndo.
-/

import Mathlib.Tactic

set_option autoImplicit false

universe u

namespace STCADR07

/-! ## Core control carrier -/

inductive ControlMode where
  | inactive
  | reloading
  | active
  | unloading
  deriving DecidableEq, Repr

inductive LandingChoice where
  | abort
  | land
  deriving DecidableEq, Repr

structure LandingWitness (S F : Type u) where
  future : F
  admissible : S → Prop

structure InFlight (I S Q V F A : Type u) where
  owner : I
  launch : S
  committed : V
  remaining : Q
  prefixUndo : A
  landingWitness : LandingWitness S F

structure ControlState (S M I Q V F E A : Type u) where
  raw : S
  traceMeta : M
  mode : ControlMode
  inFlight : Option (InFlight I S Q V F A)
  outcome : Option E

/-! The P4 result shape is mirrored locally for this standalone packet. -/

structure EffectResult (S : Type u) where
  state : S
  undo : S → S

structure Failure (S E : Type u) where
  error : E
  boundary : S
  prefixUndo : S → S

inductive ExecResult (S E : Type u) where
  | success (result : EffectResult S)
  | failure (failure : Failure S E)

/-! ## Explicit labels and typed relation witnesses -/

inductive OrchestrationLabel (I P : Type u) where
  | insert (fresh : I) (payload : P)
  | retire (owner : I)
  | remove (owner : I)
  deriving Repr

inductive LifecycleLabel (I Q V S E : Type u) where
  | begin (owner : I) (target : V)
  | iter (owner : I) (next : Q)
  | finish (owner : I)
  | divert (owner : I) (choice : LandingChoice)
  | raise (owner : I) (failure : Failure S E)
  | leave (owner : I)
  | unload (owner : I)

inductive Step
    {OL LL C : Type u}
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop) :
    C → C → Type u where
  | orchestration
      {before after : C}
      (label : OL)
      (premise : orchestration label before after) :
      Step orchestration lifecycle before after
  | lifecycle
      {before after : C}
      (label : LL)
      (premise : lifecycle label before after) :
      Step orchestration lifecycle before after

def Step.label
    {OL LL C : Type u}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before after : C} :
    Step orchestration lifecycle before after → Sum OL LL
  | .orchestration label _ => .inl label
  | .lifecycle label _ => .inr label

def Step.isLifecycle
    {OL LL C : Type u}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before after : C} :
    Step orchestration lifecycle before after → Bool
  | .orchestration _ _ => false
  | .lifecycle _ _ => true

/-! ## Finite traces and admissibility hooks -/

inductive Trace {C : Type u} (step : C → C → Type u) : C → C → Type u where
  | nil {state : C} : Trace step state state
  | cons {before middle after : C} :
      step before middle →
      Trace step middle after →
      Trace step before after

def Trace.labels
    {OL LL C : Type u}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before after : C} :
    Trace (Step orchestration lifecycle) before after → List (Sum OL LL)
  | .nil => []
  | .cons head tail => Step.label head :: Trace.labels tail

def Trace.length
    {C : Type u} {step : C → C → Type u}
    {before after : C} :
    Trace step before after → Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1

def Trace.onlyLifecycle
    {OL LL C : Type u}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before after : C} :
    Trace (Step orchestration lifecycle) before after → Prop
  | .nil => True
  | .cons (.orchestration _ _) _ => False
  | .cons (.lifecycle _ _) tail => Trace.onlyLifecycle tail

def HasLifecycleSuccessor
    {LL C : Type u}
    (lifecycle : LL → C → C → Prop)
    (state : C) : Prop :=
  ∃ label next, lifecycle label state next

def MaximalLifecycleSuffix
    {OL LL C : Type u}
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop)
    {before after : C}
    (trace : Trace (Step orchestration lifecycle) before after) : Prop :=
  trace.onlyLifecycle ∧ ¬ HasLifecycleSuccessor lifecycle after

structure TracePolicy
    (OL LL C M : Type u)
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop) where
  initial : M → Prop
  labelOk : List (Sum OL LL) → Bool
  stepOk : ∀ {before after : C}, M →
    Step orchestration lifecycle before after → Prop

def Trace.stepsOk
    {OL LL C M : Type u}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    (policy : TracePolicy OL LL C M orchestration lifecycle)
    (metadata : M)
    {before after : C} :
    Trace (Step orchestration lifecycle) before after → Prop
  | .nil => True
  | .cons head tail =>
      policy.stepOk metadata head ∧ Trace.stepsOk policy metadata tail

def Trace.admissible
    {OL LL C M : Type u}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    (policy : TracePolicy OL LL C M orchestration lifecycle)
    (metadata : M)
    {before after : C}
    (trace : Trace (Step orchestration lifecycle) before after) : Prop :=
  policy.initial metadata ∧ policy.labelOk trace.labels = true ∧
    Trace.stepsOk policy metadata trace

def lifecycleOnlyPolicy
    (OL LL C M : Type u)
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop) :
    TracePolicy OL LL C M orchestration lifecycle where
  initial := fun _ => True
  labelOk := fun labels =>
    let rec go : List (Sum OL LL) → Bool
      | [] => true
      | .inl _ :: _ => false
      | .inr _ :: rest => go rest
    go labels
  stepOk := fun {_before} {_after} _meta _step => True

theorem orchestrationTrace_not_lifecycleOnly
    {OL LL C : Type u}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before middle after : C}
    (label : OL)
    (premise : orchestration label before middle)
    (tail : Trace (Step orchestration lifecycle) middle after) :
    ¬ Trace.onlyLifecycle (.cons (.orchestration label premise) tail) := by
  simp [Trace.onlyLifecycle]

/-! ## Asynchronous landing policy -/

structure AsyncPolicy (F C : Type u) where
  atBoundary : F → C → Prop
  landingWitness : F → C → Prop
  allowed : F → C → LandingChoice → Prop
  mustLand : ∀ flight state, allowed flight state .land
  landSound : ∀ flight state, allowed flight state .land →
    landingWitness flight state
  abortGuard : ∀ flight state, allowed flight state .abort →
    atBoundary flight state

def landingAllowed {F C : Type u} (policy : AsyncPolicy F C)
    (flight : F) (state : C) (choice : LandingChoice) : Prop :=
  policy.allowed flight state choice

theorem landingAllowed_has_witness
    {F C : Type u} (policy : AsyncPolicy F C)
    (flight : F) (state : C)
    (h : landingAllowed policy flight state .land) :
    policy.landingWitness flight state := by
  exact policy.landSound flight state h

/-! ## Failure bridge to the P4-shaped result -/

def raiseLabel
    {I S E Q V : Type u}
    (owner : I) :
    ExecResult S E → Option (LifecycleLabel I Q V S E)
  | .success _ => none
  | .failure failure => some (.raise owner failure)

theorem raiseLabel_failure_preserves
    {I S E Q V : Type u}
    (owner : I) (failure : Failure S E) :
    raiseLabel (Q := Q) (V := V) owner (.failure failure : ExecResult S E) =
      some (.raise owner failure) := by
  rfl

theorem raiseLabel_success_absent
    {I S E Q V : Type u}
    (owner : I) (result : EffectResult S) :
    raiseLabel (Q := Q) (V := V) owner (.success result : ExecResult S E) = none := by
  rfl

/-! ## A finite nontrivial witness profile -/

abbrev ToyState := ControlState Nat (List Nat) Nat Nat Unit Nat Bool Nat
abbrev ToyOLabel := OrchestrationLabel Nat Unit
abbrev ToyLLabel := LifecycleLabel Nat Nat Unit Nat Bool

def toy0 : ToyState :=
  { raw := 0
    traceMeta := []
    mode := .inactive
    inFlight := none
    outcome := none }

def toyInserted : ToyState :=
  { toy0 with traceMeta := [7] }

def toyReloading : ToyState :=
  { toyInserted with
      mode := .reloading
      inFlight := some
        { owner := 7
          launch := toyInserted.raw
          committed := ()
          remaining := 0
          prefixUndo := 0
          landingWitness :=
            { future := 0
              admissible := fun _ => True } } }

def toyActive : ToyState :=
  { toyReloading with mode := .active, inFlight := none }

def toyUnloading : ToyState :=
  { toyActive with mode := .unloading }

def toyTerminal : ToyState :=
  { raw := 0
    traceMeta := []
    mode := .inactive
    inFlight := none
    outcome := none }

def toyOrchestration : ToyOLabel → ToyState → ToyState → Prop
  | .insert fresh _, before, after =>
      fresh ∉ before.traceMeta ∧
        after = { before with traceMeta := fresh :: before.traceMeta }
  | .retire owner, before, after =>
      owner ∈ before.traceMeta ∧
        after = { before with mode := .unloading }
  | .remove owner, before, after =>
      owner ∈ before.traceMeta ∧ before.mode = .inactive ∧
        after = { before with traceMeta := before.traceMeta.erase owner }

def toyLifecycle : ToyLLabel → ToyState → ToyState → Prop
  | .begin owner _, before, after =>
      owner ∈ before.traceMeta ∧ before.mode = .inactive ∧
        before.inFlight = none ∧
        after = { before with
          mode := .reloading
          inFlight := some
            { owner := owner
              launch := before.raw
              committed := ()
              remaining := 0
              prefixUndo := 0
              landingWitness :=
                { future := 0
                  admissible := fun _ => True } }
          outcome := none }
  | .iter owner next, before, after =>
      ∃ flight, before.mode = .reloading ∧
        before.inFlight = some flight ∧ flight.owner = owner ∧
        next < flight.remaining ∧
        after = { before with
          inFlight := some { flight with remaining := next } }
  | .finish owner, before, after =>
      ∃ flight, before.mode = .reloading ∧
        before.inFlight = some flight ∧ flight.owner = owner ∧
        flight.remaining = 0 ∧
        after = { before with mode := .active, inFlight := none }
  | .divert owner .abort, before, after =>
      ∃ flight, before.mode = .reloading ∧
        before.inFlight = some flight ∧ flight.owner = owner ∧
        flight.remaining = 0 ∧
        after = { before with mode := .unloading, inFlight := none }
  | .divert owner .land, before, after =>
      ∃ flight, before.mode = .reloading ∧
        before.inFlight = some flight ∧ flight.owner = owner ∧
        after = { before with mode := .active, inFlight := none }
  | .raise owner failure, before, after =>
      ∃ flight, before.mode = .reloading ∧
        before.inFlight = some flight ∧ flight.owner = owner ∧
        after = { before with
          raw := failure.boundary
          mode := .unloading
          inFlight := none
          outcome := some failure.error }
  | .leave _, before, after =>
      before.mode = .active ∧ after = { before with mode := .unloading }
  | .unload _, before, after =>
      before.mode = .unloading ∧
        after = { before with mode := .inactive, traceMeta := [] }

abbrev ToyStep := Step toyOrchestration toyLifecycle

theorem toy_insert_witness :
    toyOrchestration (.insert 7 ()) toy0 toyInserted := by
  constructor
  · simp [toy0]
  · rfl

theorem toy_begin_witness :
    toyLifecycle (.begin 7 ()) toyInserted toyReloading := by
  refine ⟨by simp [toyInserted], rfl, rfl, rfl⟩

theorem toy_finish_witness :
    toyLifecycle (.finish 7) toyReloading toyActive := by
  refine ⟨_, rfl, rfl, rfl, rfl, rfl⟩

def toyInsertStep : ToyStep toy0 toyInserted :=
  .orchestration (.insert 7 ()) toy_insert_witness

def toyBeginStep : ToyStep toyInserted toyReloading :=
  .lifecycle (.begin 7 ()) toy_begin_witness

def toyFinishStep : ToyStep toyReloading toyActive :=
  .lifecycle (.finish 7) toy_finish_witness

def toyTrace : Trace ToyStep toy0 toyActive :=
  .cons toyInsertStep (.cons toyBeginStep (.cons toyFinishStep .nil))

def toyLifecycleSuffix : Trace ToyStep toyReloading toyActive :=
  .cons toyFinishStep .nil

theorem toyTrace_has_finite_length : toyTrace.length = 3 := by
  rfl

theorem toyTrace_distinguishes_external_input :
    ¬ toyTrace.onlyLifecycle := by
  exact orchestrationTrace_not_lifecycleOnly
    (.insert 7 ()) toy_insert_witness
    (.cons toyBeginStep (.cons toyFinishStep .nil))

theorem toyLifecycleSuffix_is_admissible :
    Trace.admissible
      (lifecycleOnlyPolicy ToyOLabel ToyLLabel ToyState (List Nat)
        toyOrchestration toyLifecycle)
      toyReloading.traceMeta toyLifecycleSuffix := by
  constructor
  · trivial
  · constructor
    · rfl
    · simp [Trace.stepsOk, toyLifecycleSuffix, lifecycleOnlyPolicy]

theorem toyTerminal_has_no_lifecycle_successor :
    ¬ HasLifecycleSuccessor toyLifecycle toyTerminal := by
  intro h
  rcases h with ⟨label, after, hstep⟩
  cases label with
  | begin owner target => simp [toyLifecycle, toyTerminal] at hstep
  | iter owner next => simp [toyLifecycle, toyTerminal] at hstep
  | finish owner => simp [toyLifecycle, toyTerminal] at hstep
  | divert owner choice =>
      cases choice with
      | abort =>
          simp only [toyLifecycle, toyTerminal] at hstep
          rcases hstep with ⟨flight, hmode, _⟩
          cases hmode
      | land =>
          simp only [toyLifecycle, toyTerminal] at hstep
          rcases hstep with ⟨flight, hmode, _⟩
          cases hmode
  | raise owner failure => simp [toyLifecycle, toyTerminal] at hstep
  | leave owner => simp [toyLifecycle, toyTerminal] at hstep
  | unload owner => simp [toyLifecycle, toyTerminal] at hstep

def toyUnloadStep : ToyStep toyUnloading toyTerminal :=
  .lifecycle (.unload 7) (by
    simp [toyLifecycle, toyUnloading, toyActive, toyReloading, toyInserted, toy0,
      toyTerminal])

def toyMaximalSuffix : Trace ToyStep toyUnloading toyTerminal :=
  .cons toyUnloadStep .nil

theorem toyMaximalSuffix_is_maximal :
    MaximalLifecycleSuffix toyOrchestration toyLifecycle toyMaximalSuffix := by
  constructor
  · simp [Trace.onlyLifecycle, toyMaximalSuffix, toyUnloadStep]
  · exact toyTerminal_has_no_lifecycle_successor

def toyAsyncPolicy : AsyncPolicy
    (InFlight Nat Nat Nat Unit Nat Nat) ToyState where
  atBoundary := fun flight _ => flight.remaining = 0
  landingWitness := fun _flight _state => True
  allowed := fun flight state choice =>
    choice = .land ∨
      (choice = .abort ∧ flight.remaining = 0)
  mustLand := by
    intro flight _state
    exact Or.inl rfl
  landSound := by
    intro flight state _h
    trivial
  abortGuard := by
    intro flight _state h
    rcases h with h | h
    · cases h
    · exact h.2

theorem toy_async_forbids_midflight_abort
    (flight : InFlight Nat Nat Nat Unit Nat Nat) (state : ToyState)
    (hremaining : flight.remaining ≠ 0) :
    ¬ landingAllowed toyAsyncPolicy flight state .abort := by
  intro h
  rcases h with h | h
  · cases h
  · exact hremaining h.2

theorem toy_async_requires_landing :
    ∀ flight state, landingAllowed toyAsyncPolicy flight state .land := by
  intro flight state
  exact toyAsyncPolicy.mustLand flight state

end STCADR07
