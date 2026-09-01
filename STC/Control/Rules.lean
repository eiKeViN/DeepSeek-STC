module

public import STC.Control
public import STC.Staging
public import STC.State.Global

/-!
# Authoritative guarded global rule families

The single authoritative relation of the repaired old-paper single-realm
calculus: three orchestration constructors and eight lifecycle constructors
(the two Divert constructors map to the one printed divert case). Orchestration
allocates or erases names; lifecycle steps only edit an existing positive cell
and never allocate a name or grow the registry domain. Every constructor
carries its explicit guards, witnesses, and exact successor equation; `R.full`
is the union, `R.withdraw`/`R.iter`/`R.fail` are derived constructor views, and
`R.base` exists only as the Staging macro view over `R.full`.

## Main declarations

* `GlobalOrchestrationLabel` (insert with registrar/fresh child, retire with
  the pre-retirement inverse linkage, remove) and `GlobalLifecycleLabel`
  (begin with target view and launch token, iter with continuation and
  inverse, finish with the halt result, divertAbort with boundary evidence,
  divertLand with the landing token and inverse, raise with the failure,
  leave, unload).
* `OrchestrationRule`, `LifecycleRule` (constructor-indexed), `fullRule`,
  `globalControlModel`, `globalStep`, `globalTrace`.
* `printedCaseOf` and the Divert-to-printed-case mapping.
* `withdrawRule`, `iterationRule`, `failureRule` subfamily views with
  guard/frame theorems.
* `SelectedBody`/`ControlEdit`/`BodyClass` factorization and
  `fullRule_factorizes`; nonconstant body evidence lives in the fixture.
* `divertAdmissible` (A.async) with landing-witness and boundary-abort
  theorems.
* `globalStagingModel`, `baseOrchestrationRule`, `baseLifecycleRule`,
  `globalStutterProfile`, `globalAtomicAdequacy` (ADR-08 R.base).
* Per-constructor D48 write/read frame discharges and the lifecycle
  no-allocation/registry-domain theorems.
-/

universe u v w x y z

namespace STC.Control

open STC STC.State STC.Staging

@[expose] public section

section GlobalRules

variable {Name : Type u} {Key : Type u} {Value : Type u}
variable {Action : Type u} {Iterator : Type u} {Accumulator : Type u}
variable {Flight : Type u} {Failure : Type u} {Ambient : Type u}
variable [DecidableEq Name] [DecidableEq Key]

local notation "GState" =>
  GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient
local notation "GCell" =>
  FiberCell Name Key Value Action Iterator Accumulator Flight Failure
local notation "GSem" =>
  ComponentSemantics GState Value Action Iterator Accumulator Flight Failure

/-! ### Printed cases and boundary evidence -/

/-- The ten printed rule cases. -/
inductive PrintedCase where
  | insert
  | retire
  | remove
  | begin
  | iter
  | finish
  | divert
  | raise
  | leave
  | unload
  deriving DecidableEq, Repr

/-- The boundary evidence of a divert-abort: the target is absent, or it has
moved to a different view. -/
inductive BoundaryEvidence (Key : Type u) (Name : Type v) where
  | absent
  | changed (target : Finmap (fun _ : Key => Name))

/-! ### Labels -/

/-- Orchestration labels. `insert` retains the registrar and the fresh child;
`retire` retains the pre-retirement cell as the recorded child-retirement
inverse linkage. -/
inductive GlobalOrchestrationLabel (Name : Type u) (Cell : Type v) where
  | insert (registrar : Option Name) (fresh : Name) (child : Cell)
  | retire (owner : Name) (before : Cell)
  | remove (owner : Name)

/-- Lifecycle labels retain the target view and launch token, continuation and
inverse, halt result, boundary evidence, landing token and inverse, and the
complete failure. -/
inductive GlobalLifecycleLabel (Name : Type u) (Key : Type v) (State : Type w)
    (Iterator : Type x) (Accumulator : Type y) (Flight : Type z) (Failure : Type x) where
  | begin (owner : Name) (target : Finmap (fun _ : Key => Name)) (flight : Flight)
  | iter (owner : Name) (next : Iterator) (inverse : Accumulator) (after : State)
  | finish (owner : Name) (result : State)
  | divertAbort (owner : Name) (boundary : BoundaryEvidence Key Name)
  | divertLand (owner : Name) (landing : Flight) (inverse : Accumulator) (landed : State)
  | raise (owner : Name) (failure : Failure)
  | leave (owner : Name)
  | unload (owner : Name) (middle : State)

local notation "OLabel" => GlobalOrchestrationLabel Name GCell
local notation "LLabel" =>
  GlobalLifecycleLabel Name Key GState Iterator Accumulator Flight Failure

/-- The printed case selected by one concrete label; both Divert constructors
map to the single printed divert case. -/
def printedCaseOf : Sum OLabel LLabel → PrintedCase
  | .inl (.insert _ _ _) => .insert
  | .inl (.retire _ _) => .retire
  | .inl (.remove _) => .remove
  | .inr (.begin _ _ _) => .begin
  | .inr (.iter _ _ _ _) => .iter
  | .inr (.finish _ _) => .finish
  | .inr (.divertAbort _ _) => .divert
  | .inr (.divertLand _ _ _ _) => .divert
  | .inr (.raise _ _) => .raise
  | .inr (.leave _) => .leave
  | .inr (.unload _ _) => .unload

theorem printedCaseOf_divertAbort (owner : Name) (boundary : BoundaryEvidence Key Name) :
    printedCaseOf (.inr (.divertAbort owner boundary : LLabel)) = .divert := rfl

theorem printedCaseOf_divertLand (owner : Name) (landing : Flight) (inverse : Accumulator)
    (landed : GState) :
    printedCaseOf (.inr (.divertLand owner landing inverse landed : LLabel)) = .divert := rfl

/-- The selected owner of one lifecycle label. -/
def ownerOf : LLabel → Name
  | .begin owner _ _ => owner
  | .iter owner _ _ _ => owner
  | .finish owner _ => owner
  | .divertAbort owner _ => owner
  | .divertLand owner _ _ _ => owner
  | .raise owner _ => owner
  | .leave owner => owner
  | .unload owner _ => owner

/-! ### Successor state maps -/

/-- Edit the selected cell, leaving the state unchanged when the owner is
absent. Lifecycle successors are built from this primitive, so lifecycle rules
never allocate a name or touch the ledger/history. -/
def editCell (state : GState) (owner : Name) (edit : GCell → GCell) : GState :=
  match Finmap.lookup owner state.registry with
  | none => state
  | some cell => updateFiber state owner (edit cell)

/-- O-Remove erases only the registry entry; the ledger and history are never
erased. -/
def removeState (state : GState) (owner : Name) : GState :=
  { state with registry := Finmap.erase owner state.registry }

/-- O-Retire sets only the retired flag; it is idempotent. -/
def retireState (state : GState) (owner : Name) : GState :=
  editCell state owner (fun cell => { cell with retired := true })

/-- The begin payload: root iterator, identity accumulator, launch token. -/
def beginPayload (sem : GSem) (cell : GCell) (flight : Flight) :=
  { cell.payload with iteratorCode := cell.component.iteratorCode, accumulatorCode := sem.identityAccumulator, flightCode := some flight }

/-- L-Begin: reloading with the committed target view, the root iterator, the
identity accumulator, and the launch token. -/
def beginState (sem : GSem) (state : GState) (owner : Name)
    (ω : Finmap (fun _ : Key => Name)) (flight : Flight) : GState :=
  editCell state owner (fun cell =>
    { cell with phase := .reloading, committedView := ω, payload := beginPayload sem cell flight })

/-- The iter payload: continuation update with the composed yielded inverse. -/
def iterPayload (sem : GSem) (cell : GCell) (inverse : Accumulator) (next : Iterator) :=
  { cell.payload with iteratorCode := next, accumulatorCode := sem.composeInverse inverse cell.payload.accumulatorCode }

/-- L-Iter: the stage has already executed; the control edit updates the
continuation and composes the yielded inverse into the accumulator. -/
def iterState (sem : GSem) (state : GState) (owner : Name) (inverse : Accumulator)
    (next : Iterator) : GState :=
  editCell state owner (fun cell =>
    { cell with payload := iterPayload sem cell inverse next })

/-- L-Finish: the stage has already executed; the control edit activates. -/
def finishState (state : GState) (owner : Name) : GState :=
  editCell state owner (fun cell => { cell with phase := .active })

/-- L-DivertAbort: identity body; the control edit enters teardown. -/
def divertAbortState (state : GState) (owner : Name) : GState :=
  editCell state owner (fun cell => { cell with phase := .unloading })

/-- L-DivertLand: the landing has already executed; the control edit composes
the landing inverse and enters teardown, never activating. -/
def divertLandState (sem : GSem) (state : GState) (owner : Name) (inverse : Accumulator) :
    GState :=
  editCell state owner (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := sem.composeInverse inverse cell.payload.accumulatorCode } })

/-- L-Raise: the failure has executed (state-preservingly); the control edit
records the error and enters teardown, never failing directly. -/
def raiseState (state : GState) (owner : Name) (failure : Failure) : GState :=
  editCell state owner (fun cell =>
    { cell with phase := .unloading, payload := { cell.payload with failureData := some failure } })

/-- L-Leave: enter teardown. -/
def leaveState (state : GState) (owner : Name) : GState :=
  editCell state owner (fun cell => { cell with phase := .unloading })

/-- L-Unload: the accumulator has already executed; the control edit clears the
committed view and flight and parks the cell as inactive or failed. It never
deletes the fiber. -/
def unloadState (state : GState) (owner : Name) : GState :=
  editCell state owner (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })

/-! ### Canonical insertion cells -/

/-- The canonical initial cell of an orchestration insertion: incarnation is
the fresh name, the parent is the registrar (root or a currently registered
fiber), the birth is the next allocation index, and the cell is parked. -/
def CanonicalInitialCell (state : GState) (registrar : Option Name) (fresh : Name)
    (cell : GCell) : Prop :=
  cell.incarnation = fresh ∧ cell.parent = registrar ∧
    (match registrar with
     | some parent => Registered state parent
     | none => True) ∧
      cell.birth = nextBirth state ∧ cell.retired = false ∧ cell.phase = .inactive ∧
        cell.payload.flightCode = none ∧ cell.payload.failureData = none

/-- The boundary evidence realizes the divert-abort guard. -/
def boundaryRealizes (state : GState) (owner : Name) (cell : GCell) :
    BoundaryEvidence Key Name → Prop
  | .absent => TargetAbsent state owner
  | .changed target => TargetViewAt state owner target ∧ target ≠ cell.committedView

/-! ### The authoritative relations -/

/-- The three orchestration constructors. -/
inductive OrchestrationRule : OLabel → GState → GState → Prop where
  | insert {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {registrar : Option Name} {fresh : Name} {child : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} :
      (hfresh : Finmap.lookup fresh before.registry = none) →
      (hledger : fresh ∉ before.ledger.everIssued) →
      (hcanonical : CanonicalInitialCell before registrar fresh child) →
      (hdisjoint : ∀ (name : Name)
          (cell' : FiberCell Name Key Value Action Iterator Accumulator Flight Failure),
        Finmap.lookup name before.registry = some cell' →
          Disjoint child.component.provides cell'.component.provides) →
      OrchestrationRule (.insert registrar fresh child) before (allocate before fresh child)
  | retire {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {owner : Name} {beforeCell : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} :
      (hlook : Finmap.lookup owner before.registry = some beforeCell) →
      OrchestrationRule (.retire owner beforeCell) before (retireState before owner)
  | remove {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {owner : Name} {cell : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hretired : cell.retired = true) →
      (hphase : cell.phase = .inactive ∨ cell.phase = .failed) →
      (hnoChild : ∀ (name : Name)
          (cell' : FiberCell Name Key Value Action Iterator Accumulator Flight Failure),
        Finmap.lookup name before.registry = some cell' →
          cell'.parent = some owner → False) →
      OrchestrationRule (.remove owner) before (removeState before owner)

/-- The eight lifecycle constructors over the external stage/accumulator/
landing/failure semantics. -/
inductive LifecycleRule (sem : GSem) : LLabel → GState → GState → Prop where
  | begin {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {owner : Name} {ω : Finmap (fun _ : Key => Name)}
      {cell : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} {flight : Flight} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .inactive) →
      (hretired : cell.retired = false) →
      (htarget : TargetViewAt before owner ω) →
      (hlaunch : sem.launch before = some flight) →
      LifecycleRule sem (.begin owner ω flight) before (beginState sem before owner ω flight)
  | iter {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {owner : Name} {next : Iterator} {inverse : Accumulator}
      {cell : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} {after : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .reloading) →
      (htarget : TargetViewAt before owner cell.committedView) →
      (hstage : sem.stage cell.payload.iteratorCode before = some (.yield after inverse next)) →
      (hrank : sem.rank after < sem.rank before) →
      LifecycleRule sem (.iter owner next inverse after) before (iterState sem after owner inverse next)
  | finish {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {owner : Name} {result : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {cell : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} {inverse : Accumulator} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .reloading) →
      (htarget : TargetViewAt before owner cell.committedView) →
      (hstage : sem.stage cell.payload.iteratorCode before = some (.halt result inverse)) →

      LifecycleRule sem (.finish owner result) before (finishState result owner)
  | divertAbort {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {owner : Name} {boundary : BoundaryEvidence Key Name}
      {cell : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .reloading) →
      (hboundary : boundaryRealizes before owner cell boundary) →
      LifecycleRule sem (.divertAbort owner boundary) before (divertAbortState before owner)
  | divertLand {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {owner : Name} {landing : Flight}
      {inverse : Accumulator} {cell : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} {landed : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .reloading) →
      (hchanged : ¬ TargetViewAt before owner cell.committedView) →
      (hland : sem.flight landing before = some landed) →
      LifecycleRule sem (.divertLand owner landing inverse landed) before
        (divertLandState sem landed owner inverse)
  | raise {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {owner : Name} {failure : Failure} {cell : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .reloading ∨ cell.phase = .active) →
      (hreal : sem.failure failure before = some before) →
      LifecycleRule sem (.raise owner failure) before (raiseState before owner failure)
  | leave {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {owner : Name} {cell : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .active) →
      (hchanged : ¬ TargetViewAt before owner cell.committedView) →
      LifecycleRule sem (.leave owner) before (leaveState before owner)
  | unload {before : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} {owner : Name} {cell : FiberCell Name Key Value Action Iterator Accumulator Flight Failure} {middle : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .unloading) →
      (hfree : ¬ ∃ dependent, ReliedUpon before dependent owner) →
      (haccumulator : sem.accumulator cell.payload.accumulatorCode before = some middle) →
      LifecycleRule sem (.unload owner middle) before (unloadState middle owner)

def fullRule (sem : GSem) : Sum OLabel LLabel → GState → GState → Prop
  | .inl label, before, after => OrchestrationRule label before after
  | .inr label, before, after => LifecycleRule sem label before after

/-- The concrete `ControlModel` instance. -/
def globalControlModel (sem : GSem) : ControlModel OLabel LLabel GState :=
  { orchestration := OrchestrationRule
    lifecycle := LifecycleRule sem }

/-- Typed steps and traces over the authoritative rules. -/
abbrev globalStep (sem : GSem) :=
  Step (globalControlModel sem).orchestration (globalControlModel sem).lifecycle
abbrev globalTrace (sem : GSem) :=
  Trace (globalControlModel sem).orchestration (globalControlModel sem).lifecycle

theorem fullRule_inl (sem : GSem) (label : OLabel) (before after : GState) :
    fullRule sem (.inl label) before after ↔ OrchestrationRule label before after := by rfl

theorem fullRule_inr (sem : GSem) (label : LLabel) (before after : GState) :
    fullRule sem (.inr label) before after ↔ LifecycleRule sem label before after := by rfl

/-! ### Derived subfamily views -/

/-- `R.withdraw = Leave + Unload`. -/
def withdrawRule (sem : GSem) : LLabel → GState → GState → Prop
  | .leave owner, before, after => LifecycleRule sem (.leave owner) before after
  | .unload owner middle, before, after => LifecycleRule sem (.unload owner middle) before after
  | _, _, _ => False

/-- `R.iter = Begin + Iter + Finish + DivertAbort + DivertLand`. -/
def iterationRule (sem : GSem) : LLabel → GState → GState → Prop
  | .begin owner ω flight, before, after =>
      LifecycleRule sem (.begin owner ω flight) before after
  | .iter owner next inverse after', before, after =>
      LifecycleRule sem (.iter owner next inverse after') before after
  | .finish owner result, before, after => LifecycleRule sem (.finish owner result) before after
  | .divertAbort owner boundary, before, after =>
      LifecycleRule sem (.divertAbort owner boundary) before after
  | .divertLand owner landing inverse landed, before, after =>
      LifecycleRule sem (.divertLand owner landing inverse landed) before after
  | _, _, _ => False

/-- `R.fail = Raise`. -/
def failureRule (sem : GSem) : LLabel → GState → GState → Prop
  | .raise owner failure, before, after =>
      LifecycleRule sem (.raise owner failure) before after
  | _, _, _ => False

theorem withdrawRule_subfamily (sem : GSem) (label : LLabel) (before after : GState)
    (h : withdrawRule sem label before after) : LifecycleRule sem label before after := by
  cases label <;> simp [withdrawRule] at h ⊢
  · exact h
  · exact h

theorem iterationRule_subfamily (sem : GSem) (label : LLabel) (before after : GState)
    (h : iterationRule sem label before after) : LifecycleRule sem label before after := by
  cases label <;> simp [iterationRule] at h ⊢
  all_goals exact h

theorem failureRule_subfamily (sem : GSem) (label : LLabel) (before after : GState)
    (h : failureRule sem label before after) : LifecycleRule sem label before after := by
  cases label <;> simp [failureRule] at h ⊢
  · exact h

/-- `R.fail` ends in teardown with the error recorded, never directly failed. -/
theorem failureRule_enters_teardown (sem : GSem) {label : LLabel} {before after : GState}
    (h : failureRule sem label before after) :
    ∃ owner failure, label = .raise owner failure ∧
      ∃ cell, Finmap.lookup owner after.registry = some cell ∧ cell.phase = .unloading := by
  cases label with
  | raise owner failure =>
      simp [failureRule] at h
      cases h with
      | raise hlook _hphase _hreal =>
          refine ⟨owner, failure, rfl, ?_⟩
          unfold raiseState editCell
          rw [hlook, updateFiber_lookup_eq]
          simp
  | _ => simp [failureRule] at h

/-- The selected-body class of one concrete label. -/
inductive BodyClass where
  | identity
  | iterator
  | accumulator
  deriving DecidableEq, Repr

/-- Identity body: Insert, Retire, Remove, Begin, DivertAbort, Raise, Leave;
iterator body: Iter, Finish, DivertLand; accumulator body: Unload. -/
def bodyClassOf : Sum OLabel LLabel → BodyClass
  | .inl _ => .identity
  | .inr (.begin _ _ _) => .identity
  | .inr (.iter _ _ _ _) => .iterator
  | .inr (.finish _ _) => .iterator
  | .inr (.divertAbort _ _) => .identity
  | .inr (.divertLand _ _ _ _) => .iterator
  | .inr (.raise _ _) => .identity
  | .inr (.leave _) => .identity
  | .inr (.unload _ _) => .accumulator

/-! ### Frame and confinement theorems -/
/-! ### Frame and confinement theorems -/

theorem editCell_keys {state : GState} {owner : Name} {cell : GCell} {edit : GCell → GCell}
    (hlook : Finmap.lookup owner state.registry = some cell) :
    (editCell state owner edit).registry.keys = state.registry.keys := by
  unfold editCell
  rw [hlook, updateFiber_keys]
  apply Finset.insert_eq_self.mpr
  rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hlook]
  simp

theorem editCell_writeFrame (state : GState) (owner : Name) (edit : GCell → GCell) :
    WriteFrame state owner (editCell state owner edit) := by
  unfold WriteFrame
  constructor
  · intro name hne
    unfold editCell
    cases h : Finmap.lookup owner state.registry with
    | none => rfl
    | some cell => exact (updateFiber_lookup_ne state hne (edit cell)).symm
  · constructor
    · unfold editCell
      cases h : Finmap.lookup owner state.registry with
      | some _ => intro key _hkey; simp [updateFiber]
      | none => trivial
    · unfold editCell
      cases h : Finmap.lookup owner state.registry with
      | none => simp
      | some _ => simp [updateFiber]

theorem editCell_readNoninterference (state : GState) (owner : Name) (edit : GCell → GCell) :
    ReadNoninterference state owner (editCell state owner edit) := by
  unfold ReadNoninterference
  unfold editCell
  cases h : Finmap.lookup owner state.registry with
  | some _ => intro key _hkey; simp [updateFiber]
  | none => trivial

theorem removeState_writeFrame (state : GState) {owner : Name} {cell : GCell}
    (hlook : Finmap.lookup owner state.registry = some cell) :
    WriteFrame state owner (removeState state owner) := by
  unfold WriteFrame
  constructor
  · intro name hne
    change Finmap.lookup name state.registry =
      Finmap.lookup name (Finmap.erase owner state.registry)
    rw [Finmap.lookup_erase_ne (a := name) (a' := owner) (s := state.registry)
      (by intro h; exact hne h)]
  · constructor
    · rw [hlook]
      intro key _hkey
      simp [removeState]
    · simp [removeState]

theorem removeState_readNoninterference (state : GState) {owner : Name} {cell : GCell}
    (hlook : Finmap.lookup owner state.registry = some cell) :
    ReadNoninterference state owner (removeState state owner) := by
  unfold ReadNoninterference
  rw [hlook]
  intro key _hkey
  simp [removeState]

/-- O-Insert discharges the D48 registration frame. -/
theorem insert_registrationFrame {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after) :
    RegistrationFrame before fresh child after := by
  cases h with
  | insert hfresh hledger _hcanonical _hdisjoint =>
      exact allocate_registrationFrame before hfresh hledger

/-- O-Insert satisfies the D48 read-noninterference condition: the fresh owner
is not installed before the step. -/
theorem insert_readNoninterference {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after) :
    ReadNoninterference before fresh after := by
  cases h with
  | insert hfresh _hledger _hcanonical _hdisjoint =>
      unfold ReadNoninterference
      rw [hfresh]
      trivial

/-- O-Retire satisfies the D48 write frame: it edits only the owner's cell. -/
theorem retire_writeFrame {before after : GState} {owner : Name} {beforeCell : GCell}
    (h : OrchestrationRule (.retire owner beforeCell) before after) :
    WriteFrame before owner after := by
  cases h with
  | retire _hlook =>
      unfold retireState
      exact editCell_writeFrame before owner _

/-- O-Retire satisfies the D48 read-noninterference condition. -/
theorem retire_readNoninterference {before after : GState} {owner : Name} {beforeCell : GCell}
    (h : OrchestrationRule (.retire owner beforeCell) before after) :
    ReadNoninterference before owner after := by
  cases h with
  | retire _hlook =>
      unfold retireState
      exact editCell_readNoninterference before owner _

/-- O-Remove satisfies the D48 write frame: it erases only the owner's cell. -/
theorem remove_writeFrame {before after : GState} {owner : Name}
    (h : OrchestrationRule (.remove owner) before after) :
    WriteFrame before owner after := by
  cases h with
  | remove hlook _hretired _hphase _hnoChild => exact removeState_writeFrame before hlook

/-- O-Remove satisfies the D48 read-noninterference condition. -/
theorem remove_readNoninterference {before after : GState} {owner : Name}
    (h : OrchestrationRule (.remove owner) before after) :
    ReadNoninterference before owner after := by
  cases h with
  | remove hlook _hretired _hphase _hnoChild => exact removeState_readNoninterference before hlook

/-- Every identity-body lifecycle constructor satisfies the D48 write frame
relative to its selected owner. -/
theorem lifecycle_writeFrame (sem : GSem) {label : LLabel} {before after : GState}
    (h : LifecycleRule sem label before after)
    (hbody : bodyClassOf (.inr label) = .identity) :
    WriteFrame before (ownerOf label) after := by
  cases h <;> simp [bodyClassOf] at hbody
  · unfold beginState
    exact editCell_writeFrame _ _ _
  · unfold divertAbortState
    exact editCell_writeFrame _ _ _
  · unfold raiseState
    exact editCell_writeFrame _ _ _
  · unfold leaveState
    exact editCell_writeFrame _ _ _

/-- Every identity-body lifecycle constructor satisfies the D48
read-noninterference condition relative to its selected owner. -/
theorem lifecycle_readNoninterference (sem : GSem) {label : LLabel} {before after : GState}
    (h : LifecycleRule sem label before after)
    (hbody : bodyClassOf (.inr label) = .identity) :
    ReadNoninterference before (ownerOf label) after := by
  cases h <;> simp [bodyClassOf] at hbody
  · unfold beginState
    exact editCell_readNoninterference _ _ _
  · unfold divertAbortState
    exact editCell_readNoninterference _ _ _
  · unfold raiseState
    exact editCell_readNoninterference _ _ _
  · unfold leaveState
    exact editCell_readNoninterference _ _ _

/-- The iter control edit satisfies the D48 write frame over the stage result. -/
theorem iter_controlEdit_writeFrame (sem : GSem) (state : GState) (owner : Name)
    (inverse : Accumulator) (next : Iterator) :
    WriteFrame state owner (iterState sem state owner inverse next) := by
  unfold iterState
  exact editCell_writeFrame _ _ _

/-- The finish control edit satisfies the D48 write frame over the stage result. -/
theorem finish_controlEdit_writeFrame (state : GState) (owner : Name) :
    WriteFrame state owner (finishState state owner) := by
  unfold finishState
  exact editCell_writeFrame _ _ _

/-- The divertLand control edit satisfies the D48 write frame over the landing
result. -/
theorem divertLand_controlEdit_writeFrame (sem : GSem) (state : GState) (owner : Name)
    (inverse : Accumulator) :
    WriteFrame state owner (divertLandState sem state owner inverse) := by
  unfold divertLandState
  exact editCell_writeFrame _ _ _

/-- The unload control edit satisfies the D48 teardown frame over the
accumulator result. -/
theorem unload_controlEdit_cleanupFrame (middle : GState) (owner : Name) :
    CleanupFrame middle owner (unloadState middle owner) := by
  change CleanupFrame middle owner (editCell middle owner fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })
  unfold CleanupFrame
  constructor
  · intro name hne
    left
    unfold editCell
    cases h : Finmap.lookup owner middle.registry with
    | none => rfl
    | some cell => exact (updateFiber_lookup_ne middle hne _).symm
  · unfold editCell
    cases h : Finmap.lookup owner middle.registry with
    | none => simp
    | some _ => simp [updateFiber]

/-- Identity-body lifecycle rules never allocate a name: the registry domain,
the ledger, and the allocation history are unchanged. -/
theorem lifecycle_noAllocation (sem : GSem) {label : LLabel} {before after : GState}
    (h : LifecycleRule sem label before after)
    (hbody : bodyClassOf (.inr label) = .identity) :
    after.registry.keys = before.registry.keys ∧ after.ledger = before.ledger ∧
      after.allocationHistory = before.allocationHistory := by
  cases h with
  | begin hlook _hphase _hretired _htarget _hlaunch =>
      simp [bodyClassOf] at hbody
      rw [beginState, editCell_keys hlook]
      unfold editCell
      rw [hlook]
      simp [updateFiber]
  | iter _hlook _hphase _htarget _hstage _hrank => simp [bodyClassOf] at hbody
  | finish _hlook _hphase _htarget _hstage => simp [bodyClassOf] at hbody
  | divertAbort hlook _hphase _hboundary =>
      simp [bodyClassOf] at hbody
      rw [divertAbortState, editCell_keys hlook]
      unfold editCell
      rw [hlook]
      simp [updateFiber]
  | divertLand _hlook _hphase _hchanged _hland => simp [bodyClassOf] at hbody
  | raise hlook _hphase _hreal =>
      simp [bodyClassOf] at hbody
      rw [raiseState, editCell_keys hlook]
      unfold editCell
      rw [hlook]
      simp [updateFiber]
  | leave hlook _hphase _hchanged =>
      simp [bodyClassOf] at hbody
      rw [leaveState, editCell_keys hlook]
      unfold editCell
      rw [hlook]
      simp [updateFiber]
  | unload _hlook _hphase _hfree _haccumulator => simp [bodyClassOf] at hbody

/-- The iter control edit preserves the registry domain of the stage result. -/
theorem iter_controlEdit_domain (sem : GSem) (state : GState) (owner : Name)
    (inverse : Accumulator) (next : Iterator) :
    (iterState sem state owner inverse next).registry.keys = state.registry.keys ∧
      (iterState sem state owner inverse next).ledger = state.ledger ∧
        (iterState sem state owner inverse next).allocationHistory = state.allocationHistory := by
  unfold iterState editCell
  cases h : Finmap.lookup owner state.registry with
  | none => simp
  | some cell =>
      rw [updateFiber_keys]
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.insert_eq_self.mpr]
        rw [Finmap.mem_keys, ← Finmap.lookup_isSome, h]
        simp
      · simp [updateFiber]
      · simp [updateFiber]

/-! ### Factorization into selected body and control edit -/

def SelectedBody (sem : GSem) : Sum OLabel LLabel → GState → GState → Prop
  | .inl (.insert registrar fresh child), before, middle =>
      middle = before ∧ Finmap.lookup fresh before.registry = none ∧
        fresh ∉ before.ledger.everIssued ∧ CanonicalInitialCell before registrar fresh child ∧
          ∀ (name : Name) (cell' : GCell), Finmap.lookup name before.registry = some cell' →
            Disjoint child.component.provides cell'.component.provides
  | .inl (.retire owner beforeCell), before, middle =>
      middle = before ∧ Finmap.lookup owner before.registry = some beforeCell
  | .inl (.remove owner), before, middle =>
      middle = before ∧ ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.retired = true ∧ (cell.phase = .inactive ∨ cell.phase = .failed) ∧
          ∀ (name : Name) (cell' : GCell), Finmap.lookup name before.registry = some cell' →
            cell'.parent = some owner → False
  | .inr (.begin owner ω flight), before, middle =>
      middle = before ∧ ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .inactive ∧ cell.retired = false ∧ TargetViewAt before owner ω ∧
          sem.launch before = some flight
  | .inr (.iter owner next inverse after), before, middle =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .reloading ∧ TargetViewAt before owner cell.committedView ∧
          sem.stage cell.payload.iteratorCode before = some (.yield after inverse next) ∧
            sem.rank after < sem.rank before ∧ middle = after
  | .inr (.finish owner result), before, middle =>
      ∃ cell inverse, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .reloading ∧ TargetViewAt before owner cell.committedView ∧
          sem.stage cell.payload.iteratorCode before = some (.halt result inverse) ∧
            middle = result
  | .inr (.divertAbort owner boundary), before, middle =>
      middle = before ∧ ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .reloading ∧ boundaryRealizes before owner cell boundary
  | .inr (.divertLand owner landing _inverse landed), before, middle =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .reloading ∧ ¬ TargetViewAt before owner cell.committedView ∧
          sem.flight landing before = some landed ∧ middle = landed
  | .inr (.raise owner failure), before, middle =>
      middle = before ∧ ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        (cell.phase = .reloading ∨ cell.phase = .active) ∧
          sem.failure failure before = some before
  | .inr (.leave owner), before, middle =>
      middle = before ∧ ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .active ∧ ¬ TargetViewAt before owner cell.committedView
  | .inr (.unload owner middle'), before, middle =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .unloading ∧ (¬ ∃ dependent, ReliedUpon before dependent owner) ∧
          sem.accumulator cell.payload.accumulatorCode before = some middle ∧
            middle' = middle

/-- The control edit of a labelled step: the exact successor equation applied
to the selected body's result state. -/
def ControlEdit (sem : GSem) : Sum OLabel LLabel → GState → GState → Prop
  | .inl (.insert _registrar fresh child), middle, after =>
      after = allocate middle fresh child
  | .inl (.retire owner _beforeCell), middle, after => after = retireState middle owner
  | .inl (.remove owner), middle, after => after = removeState middle owner
  | .inr (.begin owner ω flight), middle, after =>
      after = beginState sem middle owner ω flight
  | .inr (.iter owner next inverse _after), middle, after =>
      after = iterState sem middle owner inverse next
  | .inr (.finish owner _result), middle, after => after = finishState middle owner
  | .inr (.divertAbort owner _boundary), middle, after => after = divertAbortState middle owner
  | .inr (.divertLand owner _landing inverse _landed), middle, after =>
      after = divertLandState sem middle owner inverse
  | .inr (.raise owner failure), middle, after => after = raiseState middle owner failure
  | .inr (.leave owner), middle, after => after = leaveState middle owner
  | .inr (.unload owner _middle), middle, after => after = unloadState middle owner

/-- The insert constructor factorizes through identity body and allocation edit. -/
theorem factor_insert (sem : GSem) {registrar : Option Name} {fresh : Name} {child : GCell}
    {before after : GState} :
    fullRule sem (.inl (.insert registrar fresh child)) before after ↔
      ∃ middle, SelectedBody sem (.inl (.insert registrar fresh child)) before middle ∧
        ControlEdit sem (.inl (.insert registrar fresh child)) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | insert hfresh hledger hcanonical hdisjoint =>
        refine ⟨before, ?_, ?_⟩
        · exact ⟨rfl, hfresh, hledger, hcanonical, hdisjoint⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, hfresh, hledger, hcanonical, hdisjoint⟩
    change OrchestrationRule (.insert registrar fresh child) before after
    rw [hedit, hmiddle]
    exact OrchestrationRule.insert (registrar := registrar) (fresh := fresh) (child := child)
      hfresh hledger hcanonical hdisjoint

/-- The retire constructor factorizes through identity body and flag edit. -/
theorem factor_retire (sem : GSem) {owner : Name} {beforeCell : GCell} {before after : GState} :
    fullRule sem (.inl (.retire owner beforeCell)) before after ↔
      ∃ middle, SelectedBody sem (.inl (.retire owner beforeCell)) before middle ∧
        ControlEdit sem (.inl (.retire owner beforeCell)) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | retire hlook =>
        refine ⟨before, ?_, ?_⟩
        · exact ⟨rfl, hlook⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, hlook⟩
    change OrchestrationRule (.retire owner beforeCell) before after
    rw [hedit, hmiddle]
    exact OrchestrationRule.retire hlook

/-- The remove constructor factorizes through identity body and erasure edit. -/
theorem factor_remove (sem : GSem) {owner : Name} {before after : GState} :
    fullRule sem (.inl (.remove owner)) before after ↔
      ∃ middle, SelectedBody sem (.inl (.remove owner)) before middle ∧
        ControlEdit sem (.inl (.remove owner)) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | remove hlook hretired hphase hnoChild =>
        refine ⟨before, ?_, ?_⟩
        · exact ⟨rfl, _, hlook, hretired, hphase, hnoChild⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, cell, hlook, hretired, hphase, hnoChild⟩
    change OrchestrationRule (.remove owner) before after
    rw [hedit, hmiddle]
    exact OrchestrationRule.remove hlook hretired hphase hnoChild

/-- The begin constructor factorizes through identity body and launch edit. -/
theorem factor_begin (sem : GSem) {owner : Name} {ω : Finmap (fun _ : Key => Name)}
    {flight : Flight} {before after : GState} :
    fullRule sem (.inr (.begin owner ω flight)) before after ↔
      ∃ middle, SelectedBody sem (.inr (.begin owner ω flight)) before middle ∧
        ControlEdit sem (.inr (.begin owner ω flight)) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | begin hlook hphase hretired htarget hlaunch =>
        refine ⟨before, ?_, ?_⟩
        · exact ⟨rfl, _, hlook, hphase, hretired, htarget, hlaunch⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, cell, hlook, hphase, hretired, htarget, hlaunch⟩
    change LifecycleRule sem (.begin owner ω flight) before after
    rw [hedit, hmiddle]
    exact LifecycleRule.begin hlook hphase hretired htarget hlaunch

/-- The iter constructor factorizes through a real yielding stage and the
continuation edit. -/
theorem factor_iter (sem : GSem) {owner : Name} {next : Iterator} {inverse : Accumulator}
    {after' : GState} {before after : GState} :
    fullRule sem (.inr (.iter owner next inverse after')) before after ↔
      ∃ middle, SelectedBody sem (.inr (.iter owner next inverse after')) before middle ∧
        ControlEdit sem (.inr (.iter owner next inverse after')) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | iter hlook hphase htarget hstage hrank =>
        refine ⟨after', ?_, ?_⟩
        · exact ⟨_, hlook, hphase, htarget, hstage, hrank, rfl⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨cell, hlook, hphase, htarget, hstage, hrank, hmiddle⟩
    change LifecycleRule sem (.iter owner next inverse after') before after
    rw [hedit, hmiddle]
    exact LifecycleRule.iter hlook hphase htarget hstage hrank

/-- The finish constructor factorizes through a real halting stage and the
activation edit. -/
theorem factor_finish (sem : GSem) {owner : Name} {result : GState} {before after : GState} :
    fullRule sem (.inr (.finish owner result)) before after ↔
      ∃ middle, SelectedBody sem (.inr (.finish owner result)) before middle ∧
        ControlEdit sem (.inr (.finish owner result)) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | finish hlook hphase htarget hstage =>
        refine ⟨result, ?_, ?_⟩
        · exact ⟨_, _, hlook, hphase, htarget, hstage, rfl⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨cell, inverse, hlook, hphase, htarget, hstage, hmiddle⟩
    change LifecycleRule sem (.finish owner result) before after
    rw [hedit, hmiddle]
    exact LifecycleRule.finish hlook hphase htarget hstage

/-- The divertAbort constructor factorizes through identity body and teardown
edit. -/
theorem factor_divertAbort (sem : GSem) {owner : Name} {boundary : BoundaryEvidence Key Name}
    {before after : GState} :
    fullRule sem (.inr (.divertAbort owner boundary)) before after ↔
      ∃ middle, SelectedBody sem (.inr (.divertAbort owner boundary)) before middle ∧
        ControlEdit sem (.inr (.divertAbort owner boundary)) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | divertAbort hlook hphase hboundary =>
        refine ⟨before, ?_, ?_⟩
        · exact ⟨rfl, _, hlook, hphase, hboundary⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, cell, hlook, hphase, hboundary⟩
    change LifecycleRule sem (.divertAbort owner boundary) before after
    rw [hedit, hmiddle]
    exact LifecycleRule.divertAbort hlook hphase hboundary

/-- The divertLand constructor factorizes through a real landing and the
inverse-composing teardown edit. -/
theorem factor_divertLand (sem : GSem) {owner : Name} {landing : Flight}
    {inverse : Accumulator} {landed : GState} {before after : GState} :
    fullRule sem (.inr (.divertLand owner landing inverse landed)) before after ↔
      ∃ middle, SelectedBody sem (.inr (.divertLand owner landing inverse landed)) before middle ∧
        ControlEdit sem (.inr (.divertLand owner landing inverse landed)) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | divertLand hlook hphase hchanged hland =>
        refine ⟨landed, ?_, ?_⟩
        · exact ⟨_, hlook, hphase, hchanged, hland, rfl⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨cell, hlook, hphase, hchanged, hland, hmiddle⟩
    change LifecycleRule sem (.divertLand owner landing inverse landed) before after
    rw [hedit, hmiddle]
    exact LifecycleRule.divertLand hlook hphase hchanged hland

/-- The raise constructor factorizes through identity body and the error edit. -/
theorem factor_raise (sem : GSem) {owner : Name} {failure : Failure} {before after : GState} :
    fullRule sem (.inr (.raise owner failure)) before after ↔
      ∃ middle, SelectedBody sem (.inr (.raise owner failure)) before middle ∧
        ControlEdit sem (.inr (.raise owner failure)) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | raise hlook hphase hreal =>
        refine ⟨before, ?_, ?_⟩
        · exact ⟨rfl, _, hlook, hphase, hreal⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, cell, hlook, hphase, hreal⟩
    change LifecycleRule sem (.raise owner failure) before after
    rw [hedit, hmiddle]
    exact LifecycleRule.raise hlook hphase hreal

/-- The leave constructor factorizes through identity body and teardown edit. -/
theorem factor_leave (sem : GSem) {owner : Name} {before after : GState} :
    fullRule sem (.inr (.leave owner)) before after ↔
      ∃ middle, SelectedBody sem (.inr (.leave owner)) before middle ∧
        ControlEdit sem (.inr (.leave owner)) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | leave hlook hphase hchanged =>
        refine ⟨before, ?_, ?_⟩
        · exact ⟨rfl, _, hlook, hphase, hchanged⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, cell, hlook, hphase, hchanged⟩
    change LifecycleRule sem (.leave owner) before after
    rw [hedit, hmiddle]
    exact LifecycleRule.leave hlook hphase hchanged

/-- The unload constructor factorizes through the accumulator and the
view-clearing teardown edit. -/
theorem factor_unload (sem : GSem) {owner : Name} {middle' : GState} {before after : GState} :
    fullRule sem (.inr (.unload owner middle')) before after ↔
      ∃ middle, SelectedBody sem (.inr (.unload owner middle')) before middle ∧
        ControlEdit sem (.inr (.unload owner middle')) middle after := by
  constructor
  · intro h
    simp [fullRule] at h
    cases h with
    | unload hlook hphase hfree haccumulator =>
        refine ⟨middle', ?_, ?_⟩
        · exact ⟨_, hlook, hphase, hfree, haccumulator, rfl⟩
        · rfl
  · intro h
    rcases h with ⟨middle, hbody, hedit⟩
    rcases hbody with ⟨cell, hlook, hphase, hfree, haccumulator, hmiddle⟩
    change LifecycleRule sem (.unload owner middle') before after
    rw [hedit, hmiddle]
    exact LifecycleRule.unload hlook hphase hfree haccumulator

/-- `R.full` factorizes through the selected body and the control edit; the
decomposition is derived by cases over the constructors, never assumed. -/
theorem fullRule_factorizes (sem : GSem) {label : Sum OLabel LLabel} {before after : GState} :
    fullRule sem label before after ↔
      ∃ middle, SelectedBody sem label before middle ∧ ControlEdit sem label middle after := by
  cases label with
  | inl l =>
      cases l with
      | insert registrar fresh child => exact factor_insert sem
      | retire owner beforeCell => exact factor_retire sem
      | remove owner => exact factor_remove sem
  | inr l =>
      cases l with
      | begin owner ω flight => exact factor_begin sem
      | iter owner next inverse after' => exact factor_iter sem
      | finish owner result => exact factor_finish sem
      | divertAbort owner boundary => exact factor_divertAbort sem
      | divertLand owner landing inverse landed => exact factor_divertLand sem
      | raise owner failure => exact factor_raise sem
      | leave owner => exact factor_leave sem
      | unload owner middle' => exact factor_unload sem

/-! ### A.async: admissible divert policy -/

/-- A.async: divert admissibility over the frozen `AsyncPolicy`. Landing is
always retained and bound to the policy's landing witness; abort is allowed
only at the boundary. -/
def divertAdmissible (_sem : GSem) (policy : AsyncPolicy Flight GState) :
    Sum OLabel LLabel → GState → Prop
  | .inr (.divertLand owner landing _ _), state =>
      ∃ cell, Finmap.lookup owner state.registry = some cell ∧
        cell.payload.flightCode = some landing ∧ cell.phase = .reloading ∧
          policy.allowed landing state .land
  | .inr (.divertAbort owner _), state =>
      ∃ cell flight, Finmap.lookup owner state.registry = some cell ∧
        cell.payload.flightCode = some flight ∧ cell.phase = .reloading ∧
          policy.allowed flight state .abort
  | _, _ => False

/-- An admissible landing carries the policy's landing witness. -/
theorem divertLand_has_landingWitness (sem : GSem) (policy : AsyncPolicy Flight GState)
    {state : GState} {owner : Name} {landing : Flight} {inverse : Accumulator} {landed : GState} :
    divertAdmissible sem policy (.inr (.divertLand owner landing inverse landed)) state →
      ∃ cell, Finmap.lookup owner state.registry = some cell ∧
        cell.payload.flightCode = some landing ∧ policy.landingWitness landing state := by
  intro h
  rcases h with ⟨cell, hlook, hflight, _hphase, hallowed⟩
  exact ⟨cell, hlook, hflight, policy.landSound landing state hallowed⟩

/-- An admissible abort sits at the policy's boundary. -/
theorem divertAbort_atBoundary (sem : GSem) (policy : AsyncPolicy Flight GState)
    {state : GState} {owner : Name} {boundary : BoundaryEvidence Key Name} :
    divertAdmissible sem policy (.inr (.divertAbort owner boundary)) state →
      ∃ cell flight, Finmap.lookup owner state.registry = some cell ∧
        cell.payload.flightCode = some flight ∧ policy.atBoundary flight state := by
  intro h
  rcases h with ⟨cell, flight, hlook, hflight, _hphase, hallowed⟩
  exact ⟨cell, flight, hlook, hflight, policy.abortGuard flight state hallowed⟩

/-- DivertLand never reclassifies a pending path as success: it enters
teardown, never the active phase. -/
theorem divertLand_not_active (sem : GSem) {owner : Name} {landing : Flight}
    {inverse : Accumulator} {landed before after : GState} {cell cell' : GCell}
    (h : LifecycleRule sem (.divertLand owner landing inverse landed) before after)
    (hlook' : Finmap.lookup owner landed.registry = some cell')
    (hlook : Finmap.lookup owner after.registry = some cell) :
    cell.phase = .unloading := by
  cases h with
  | divertLand _hlook _hphase _hchanged _hland =>
      unfold divertLandState editCell at hlook
      rw [hlook', updateFiber_lookup_eq] at hlook
      have hcell := (Option.some.inj hlook).symm
      rw [hcell]

/-- Raise never reclassifies a failing path as success: it enters teardown
with the error recorded, never the failed phase directly. -/
theorem raise_not_failed (sem : GSem) {owner : Name} {failure : Failure} {before after : GState}
    {cell : GCell} (h : LifecycleRule sem (.raise owner failure) before after)
    (hlook : Finmap.lookup owner after.registry = some cell) :
    cell.phase = .unloading ∧ cell.payload.failureData = some failure := by
  cases h with
  | raise hlook' _hphase _hreal =>
      unfold raiseState editCell at hlook
      rw [hlook', updateFiber_lookup_eq] at hlook
      have hcell := (Option.some.inj hlook).symm
      rw [hcell]
      simp

/-! ### R.base: the Staging macro view -/

/-- The ADR-08 base model: base steps are singleton macro paths over `R.full`,
with the reloading iter step as the only permitted stutter. All carriers share
one universe, so the frozen single-universe `StagingModel` carrier applies. -/
def globalStagingModel (sem : GSem) :
    StagingModel GState GState OLabel OLabel LLabel LLabel :=
  { embed := id
    project := fun state => some state
    stable := fun _ => True
    fullOrch := OrchestrationRule
    fullLife := LifecycleRule sem
    expandOrch := fun label => [.inl label]
    expandLife := fun label => [.inr label]
    atomicOrch := fun labels => ∃ label, labels = [.inl label]
    atomicLife := fun labels => ∃ label, labels = [.inr label]
    project_embed := by intro base; rfl
    stable_embed := by intro base; trivial }

/-- `R.base`: the base orchestration relation, derived only through
`Staging.MacroPath`. -/
def baseOrchestrationRule (sem : GSem) := RbOrch (globalStagingModel sem)

/-- `R.base`: the base lifecycle relation, derived only through
`Staging.MacroPath`. -/
def baseLifecycleRule (sem : GSem) := RbLife (globalStagingModel sem)

/-- A singleton orchestration macro path is exactly one full orchestration
step. -/
theorem singletonPath_orchestration (sem : GSem) {before after : GState} {label : OLabel} :
    Nonempty (MacroPath (globalStagingModel sem) [.inl label] before after) →
      OrchestrationRule label before after := by
  rintro ⟨path⟩
  rcases path with ⟨trace, hlabels⟩
  cases trace with
  | nil => simp [Trace.labels] at hlabels
  | cons head tail =>
      cases tail with
      | nil =>
          cases head with
          | orchestration label' hpremise =>
              have hlabels' : label' = label := by
                simpa [globalStagingModel, Trace.labels, Step.label] using hlabels
              simpa [globalStagingModel, hlabels'] using hpremise
          | lifecycle label' hpremise =>
              simp [Trace.labels, Step.label] at hlabels
      | cons _ _ => simp [Trace.labels] at hlabels

/-- A singleton lifecycle macro path is exactly one full lifecycle step. -/
theorem singletonPath_lifecycle (sem : GSem) {before after : GState} {label : LLabel} :
    Nonempty (MacroPath (globalStagingModel sem) [.inr label] before after) →
      LifecycleRule sem label before after := by
  rintro ⟨path⟩
  rcases path with ⟨trace, hlabels⟩
  cases trace with
  | nil => simp [Trace.labels] at hlabels
  | cons head tail =>
      cases tail with
      | nil =>
          cases head with
          | orchestration label' hpremise =>
              simp [Trace.labels, Step.label] at hlabels
          | lifecycle label' hpremise =>
              have hlabels' : label' = label := by
                simpa [globalStagingModel, Trace.labels, Step.label] using hlabels
              simpa [globalStagingModel, hlabels'] using hpremise
      | cons _ _ => simp [Trace.labels] at hlabels

/-- A base orchestration step is exactly one full orchestration step. -/
theorem baseOrchestration_iff (sem : GSem) (label : OLabel) (before after : GState) :
    baseOrchestrationRule sem label before after ↔ OrchestrationRule label before after := by
  unfold baseOrchestrationRule RbOrch AtomicOrchMacro
  constructor
  · intro h
    rcases h with ⟨_hatomic, hpath⟩
    exact singletonPath_orchestration sem (by simpa [globalStagingModel] using hpath)
  · intro h
    refine ⟨⟨label, rfl⟩, ?_⟩
    refine ⟨Trace.cons (Step.orchestration label h) Trace.nil, ?_⟩
    rfl

/-- A base lifecycle step is exactly one full lifecycle step. -/
theorem baseLifecycle_iff (sem : GSem) (label : LLabel) (before after : GState) :
    baseLifecycleRule sem label before after ↔ LifecycleRule sem label before after := by
  unfold baseLifecycleRule RbLife AtomicLifeMacro
  constructor
  · intro h
    rcases h with ⟨_hatomic, hpath⟩
    exact singletonPath_lifecycle sem (by simpa [globalStagingModel] using hpath)
  · intro h
    refine ⟨⟨label, rfl⟩, ?_⟩
    refine ⟨Trace.cons (Step.lifecycle label h) Trace.nil, ?_⟩
    rfl

/-- The profile-tagged stutter permission: orchestration never stutters; a
lifecycle stutter must be a real full lifecycle step with equal endpoints. -/
def globalStutterProfile (sem : GSem) : StutterProfile (globalStagingModel sem) :=
  { Tag := LLabel
    orchestration := fun _tag _labels _before => False
    lifecycle := fun tag labels before =>
      labels = [.inr tag] ∧ LifecycleRule sem tag before before }

/-- ADR-08 adequacy, orchestration half: every atomic orchestration macro path
is exactly one base step. -/
theorem orchestrationAdequacy (sem : GSem) {before after : GState}
    {labels : List (Sum OLabel LLabel)} (hatomic : (globalStagingModel sem).atomicOrch labels)
    (path : MacroPath (globalStagingModel sem) labels before after) :
    ∃ label, labels = (globalStagingModel sem).expandOrch label ∧
      RbOrch (globalStagingModel sem) label before after := by
  rcases hatomic with ⟨label, hlabels⟩
  refine ⟨label, ?_, ?_⟩
  · simpa [globalStagingModel] using hlabels
  · exact (baseOrchestration_iff sem label before after).mpr
      (singletonPath_orchestration sem (by
        rw [hlabels] at path
        exact ⟨path⟩))

/-- ADR-08 adequacy, lifecycle half: every atomic lifecycle macro path is
either a tagged stutter or exactly one base step. -/
theorem lifecycleAdequacy (sem : GSem) {before after : GState}
    {labels : List (Sum OLabel LLabel)} (hatomic : (globalStagingModel sem).atomicLife labels)
    (path : MacroPath (globalStagingModel sem) labels before after) :
    (∃ tag, (globalStutterProfile sem).lifecycle tag labels before ∧ before = after) ∨
      ∃ label, labels = (globalStagingModel sem).expandLife label ∧
        RbLife (globalStagingModel sem) label before after := by
  rcases hatomic with ⟨label, hlabels⟩
  by_cases hsame : before = after
  · left
    refine ⟨label, ?_, hsame⟩
    constructor
    · simpa [globalStagingModel] using hlabels
    · have hstep : LifecycleRule sem label before after := singletonPath_lifecycle sem (by
        rw [hlabels] at path
        exact ⟨path⟩)
      simpa [hsame] using hstep
  · right
    refine ⟨label, ?_, ?_⟩
    · simpa [globalStagingModel] using hlabels
    · exact (baseLifecycle_iff sem label before after).mpr
        (singletonPath_lifecycle sem (by
          rw [hlabels] at path
          exact ⟨path⟩))

/-- ADR-08 adequacy: every atomic macro path is either a tagged stutter or
exactly one base step. -/
theorem globalAtomicAdequacy (sem : GSem) :
    AtomicAdequacy (globalStagingModel sem) (globalStutterProfile sem) := by
  constructor
  · intro before after labels hatomic path
    exact Or.inr (orchestrationAdequacy sem hatomic (by simpa [globalStagingModel] using path))
  · intro before after labels hatomic path
    exact lifecycleAdequacy sem hatomic (by simpa [globalStagingModel] using path)

end GlobalRules

end

end STC.Control
