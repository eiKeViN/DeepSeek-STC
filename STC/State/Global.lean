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
  registry : Finmap (fun _ : Name => Fiber Name Key Value Action Iterator Accumulator Flight Failure)
  coeffects : Finmap (fun _ : Key => Value)
  ledger : NameLedger Name
  allocationHistory : List Name

/-- The ordered allocation history is an immutable state component. -/
def issuedInOrder (state : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient) :
    List Name := state.allocationHistory

/-- Active names are derived by inspecting the positive registry cells. -/
noncomputable def activeNames (state : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient) :
    Finset Name := by
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

noncomputable def activeStore (state : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient) :
    ActiveStoreView Name :=
  { active := activeNames state, ordered := state.allocationHistory.filter (fun n => n ∈ activeNames state) }

/-- Explicit local/global well-formedness profile. -/
structure WellFormedProfile
    (Name : Type u) (Key : Type v) (Value : Type w)
    (Action : Type u) (Iterator : Type v) (Accumulator : Type w)
    (Flight : Type u) (Failure : Type v) (Ambient : Type x)
    [DecidableEq Name] [DecidableEq Key] where
  parentClosed : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  parentAcyclic : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  tableConfined : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  provisionDisjoint : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  lifecycleCoherent : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  committedViewClosed : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  committedProvidersClosed : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  root : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  declarations : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop

def WellFormed (profile : WellFormedProfile Name Key Value Action Iterator Accumulator Flight Failure Ambient)
    (state : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient) : Prop :=
  profile.parentClosed state ∧ profile.parentAcyclic state ∧ profile.tableConfined state ∧
    profile.provisionDisjoint state ∧ profile.lifecycleCoherent state ∧
      profile.committedViewClosed state ∧ profile.committedProvidersClosed state ∧
        profile.root state ∧ profile.declarations state

/-- Provider relation over a state and a declared requirement key. -/
def ProvidesNow (state : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient)
    (provider : Name) (key : Key) : Prop :=
  ∃ fiber, Finmap.lookup provider state.registry = some fiber ∧
    key ∈ fiber.component.provides ∧ fiber.phase = .active ∧ !fiber.retired

/-- An executable provider selector and its well-formed-relative contract. -/
structure ProviderModel
    (profile : WellFormedProfile Name Key Value Action Iterator Accumulator Flight Failure Ambient) where
  providerOf : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient →
    Key → Option Name
  sound : ∀ {state provider key}, WellFormed profile state →
    providerOf state key = some provider → ProvidesNow state provider key
  complete : ∀ {state provider key}, WellFormed profile state →
    ProvidesNow state provider key → providerOf state key = some provider
  unique : ∀ {state key left right}, WellFormed profile state →
    ProvidesNow state left key → ProvidesNow state right key → left = right

/-- A target/quiescence projection used by the derived Staging view. -/
def TargetView (state : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient) :
    Finset Name := state.registry.keys

def Quiescent (state : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient) : Prop :=
  ∀ name fiber, Finmap.lookup name state.registry = some fiber →
    fiber.phase ≠ .reloading ∧ fiber.phase ≠ .unloading ∧ fiber.payload.flightCode = none

/-- A state update that changes only the selected registry cell. -/
def updateFiber (state : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient)
    (name : Name) (fiber : FiberCell Name Key Value Action Iterator Accumulator Flight Failure) :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient :=
  { state with registry := Finmap.insert name fiber state.registry }

theorem updateFiber_coeffects (state : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient)
    (name : Name) (fiber : FiberCell Name Key Value Action Iterator Accumulator Flight Failure) :
    (updateFiber state name fiber).coeffects = state.coeffects := rfl

/-- Explicit alpha action for a name-bearing code. -/
structure AlphaCodeProfile (Name : Type u) (Code : Type v) where
  act : Equiv.Perm Name → Code → Code
  identity : ∀ code, act (Equiv.refl Name) code = code
  composition : ∀ (χ ψ : Equiv.Perm Name) code,
    act (χ * ψ) code = act χ (act ψ code)
  equivariant : Prop

/-- Replayable selected-body factorization. The nonconstant obligation is
separate so a later proof cannot silently use a constant successor witness. -/
structure FactorizationProfile (State Code : Type u) where
  replay : Code → State → State
  controlEdit : Code → State → State
  frame : Prop
  replay_equation : Prop
  nonconstant : Prop

/-- Existence/landing obligations used by the progress lane. -/
structure ProgressProfile (State : Type u) where
  lifecycleReady : State → Prop
  beginExists : ∀ state, lifecycleReady state → Prop
  iterExists : ∀ state, lifecycleReady state → Prop
  finishExists : ∀ state, lifecycleReady state → Prop
  cleanupExists : ∀ state, lifecycleReady state → Prop
  landingOrAbort : Prop

/-- Semantic determinism and continuation/landing coherence for confluence. -/
structure ConfluenceProfile (State Witness : Type u) where
  resultDeterministic : State → Witness → Witness → Prop
  continuationCoherent : Prop
  landingCoherent : Prop

end Global

end

end STC.State
