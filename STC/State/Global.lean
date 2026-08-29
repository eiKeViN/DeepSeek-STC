module

public import STC.State.Fiber
public import STC.State.FinmapAdapter

/-!
# Positive global state

`GlobalState` combines the finite fiber registry, dependent coeffect store,
lifetime freshness ledger, and immutable allocation history. Well-formedness is
an explicit conjunction of local predicates and never hides a support order.
-/

universe u v w x

namespace STC.State

@[expose] public section

section Global

variable {Name : Type u} {Key : Type v} {Value : Type w}
variable {Action : Type u} {Iterator : Type v} {Accumulator : Type w}
variable {Flight : Type u} {Failure : Type v} {Ambient : Type x}
variable [DecidableEq Name] [DecidableEq Key]

abbrev Fiber (Name : Type u) (Key : Type v) (Value : Type w)
    (Action : Type u) (Iterator : Type v) (Accumulator : Type w)
    (Flight : Type u) (Failure : Type v) :=
  FiberCell Name Key Value Action Iterator Accumulator Flight Failure

/-- Global state with only positive/data fields. -/
structure GlobalState (Name : Type u) (Key : Type v) (Value : Type w)
    (Action : Type u) (Iterator : Type v) (Accumulator : Type w)
    (Flight : Type u) (Failure : Type v) (Ambient : Type x)
    [DecidableEq Name] [DecidableEq Key] where
  ambient : Ambient
  registry :
    Finmap (fun _ : Name => Fiber Name Key Value Action Iterator Accumulator Flight Failure)
  coeffects : Finmap (fun _ : Key => Value)
  ledger : NameLedger Name
  allocationHistory : List Name

local notation "GState" =>
  GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient

/-- The ordered allocation history is an immutable state component. -/
def issuedInOrder (state : GState) : List Name := state.allocationHistory

/-- Active names are derived by inspecting the positive registry cells. -/
noncomputable def activeNames (state : GState) : Finset Name := by
  classical
  exact
  state.registry.keys.filter (fun name =>
    match Finmap.lookup name state.registry with
    | some fiber => fiber.phase = .active ∧ fiber.retired = false
    | none => False)

/-- A derived active-store view; it does not replace the authoritative registry. -/
structure ActiveStoreView (Name : Type u) where
  active : Finset Name
  ordered : List Name

noncomputable def activeStore (state : GState) : ActiveStoreView Name :=
  { active := activeNames state
    ordered := state.allocationHistory.filter (fun n => n ∈ activeNames state) }

/-- Explicit local/global well-formedness profile. -/
structure WellFormedProfile
    (Name : Type u) (Key : Type v) (Value : Type w)
    (Action : Type u) (Iterator : Type v) (Accumulator : Type w)
    (Flight : Type u) (Failure : Type v) (Ambient : Type x)
    [DecidableEq Name] [DecidableEq Key] where
  parentClosed :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  parentAcyclic :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  tableConfined :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  provisionDisjoint :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  lifecycleCoherent :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  committedViewClosed :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  committedProvidersClosed :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  root : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  declarations :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop

def WellFormed
    (profile : WellFormedProfile Name Key Value Action Iterator Accumulator Flight Failure Ambient)
    (state :
      GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient) : Prop :=
  profile.parentClosed state ∧ profile.parentAcyclic state ∧ profile.tableConfined state ∧
    profile.provisionDisjoint state ∧ profile.lifecycleCoherent state ∧
      profile.committedViewClosed state ∧ profile.committedProvidersClosed state ∧
        profile.root state ∧ profile.declarations state

/-- Provider relation over a state and a declared requirement key. -/
def ProvidesNow (state : GState) (provider : Name) (key : Key) : Prop :=
  ∃ fiber, Finmap.lookup provider state.registry = some fiber ∧
    key ∈ fiber.component.provides ∧ fiber.phase = .active ∧ !fiber.retired

/-- An executable provider selector and its well-formed-relative contract. -/
structure ProviderModel
    (profile :
      WellFormedProfile Name Key Value Action Iterator Accumulator Flight Failure Ambient) where
  providerOf : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient →
    Key → Option Name
  sound : ∀ {state provider key}, WellFormed profile state →
    providerOf state key = some provider → ProvidesNow state provider key
  complete : ∀ {state provider key}, WellFormed profile state →
    ProvidesNow state provider key → providerOf state key = some provider
  unique : ∀ {state key left right}, WellFormed profile state →
    ProvidesNow state left key → ProvidesNow state right key → left = right

/-- A target/quiescence projection used by the derived Staging view. -/
def TargetView (state : GState) : Finset Name := state.registry.keys

def Quiescent (state : GState) : Prop :=
  ∀ name fiber, Finmap.lookup name state.registry = some fiber →
    fiber.phase ≠ .reloading ∧ fiber.phase ≠ .unloading ∧ fiber.payload.flightCode = none

/-- A state update that changes only the selected registry cell. -/
def updateFiber (state : GState)
    (name : Name) (fiber : FiberCell Name Key Value Action Iterator Accumulator Flight Failure) :
    GState :=
  { state with registry := Finmap.insert name fiber state.registry }

theorem updateFiber_coeffects (state : GState)
    (name : Name) (fiber : FiberCell Name Key Value Action Iterator Accumulator Flight Failure) :
    (updateFiber state name fiber).coeffects = state.coeffects := rfl

/-- Explicit alpha action and interpreter equivariance for a name-bearing code. -/
structure AlphaCodeProfile (Name : Type u) (Code : Type v) (State : Type w) where
  act : Equiv.Perm Name → Code → Code
  stateAction : AlphaAction Name State
  interprets : Code → State → State → Prop
  identity : ∀ code, act (Equiv.refl Name) code = code
  composition : ∀ (χ ψ : Equiv.Perm Name) code,
    act (χ * ψ) code = act χ (act ψ code)
  equivariant : ∀ χ code before after, interprets code before after →
    interprets (act χ code) (stateAction.act χ before) (stateAction.act χ after)

/-- Replayable selected-body factorization. The nonconstant obligation is
separate so a later proof cannot silently use a constant successor witness. -/
structure FactorizationProfile (State Code : Type u) where
  selectedMap : Code → State → State
  controlEdit : Code → State → State
  replay : Code → State → State
  frame : Code → State → State → Prop
  replay_equation : ∀ code state,
    replay code state = controlEdit code (selectedMap code state)
  frame_holds : ∀ code state, frame code state (replay code state)
  nonconstant : ∃ code left right,
    left ≠ right ∧ selectedMap code left ≠ selectedMap code right

/-- Existence/landing obligations used by the progress lane. -/
structure ProgressProfile (State : Type u) where
  lifecycleReady : State → Prop
  beginStep : State → State → Prop
  iterStep : State → State → Prop
  finishStep : State → State → Prop
  cleanupStep : State → State → Prop
  boundaryAbort : State → State → Prop
  beginExists : ∀ state, lifecycleReady state → ∃ after, beginStep state after
  iterExists : ∀ state, lifecycleReady state → ∃ after, iterStep state after
  finishExists : ∀ state, lifecycleReady state → ∃ after, finishStep state after
  cleanupExists : ∀ state, lifecycleReady state → ∃ after, cleanupStep state after
  landingOrAbort : ∀ state, lifecycleReady state →
    ∃ after, finishStep state after ∨ boundaryAbort state after

/-- Semantic determinism and continuation/landing coherence for confluence. -/
structure ConfluenceProfile (State Witness : Type u) where
  observes : State → State → Prop
  resolves : State → Witness → State → Prop
  continuation : State → State → Prop
  landing : State → State → Prop
  resultDeterministic : ∀ {source left right wl wr},
    resolves source wl left → resolves source wr right → observes left right
  continuationCoherent : ∀ {left right}, observes left right → continuation left right
  landingCoherent : ∀ {left right}, observes left right → landing left right

end Global

end

end STC.State
