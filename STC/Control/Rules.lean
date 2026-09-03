module

public import STC.Control
public import STC.Staging
public import STC.State.Global

/-!
# Authoritative guarded global rule families

The single authoritative relation of the repaired old-paper single-realm
calculus: three orchestration constructors and eight lifecycle constructors
(the two Divert constructors map to the one printed divert case). Labels name
OPERATIONS only — codes, tokens, targets, and complete failure evidence —
never the success endpoints; every state-valued witness (`after`, `result`,
`landed`, `middle`, the launch token, the stage/landing inverses) is bound by
the rule-local semantic witness. Orchestration allocates or erases names;
lifecycle steps only edit an existing positive cell and never allocate a name
or grow the registry domain. Every constructor carries its explicit guards,
witnesses, and exact successor equation; `R.full` is the union,
`R.withdraw`/`R.iter`/`R.fail` are derived constructor views, and `R.base`
exists only as the Staging macro view over `R.full` (Reload = Begin·Finish,
Unload = Leave·Unload).

## Main declarations

* `GlobalOrchestrationLabel` (insert with registrar/fresh child, retire,
  remove) and `GlobalLifecycleLabel` (begin with target view, iter with
  continuation, finish, divertAbort with boundary evidence, divertLand with
  the landing token, raise with the complete failure, leave, unload).
* `OrchestrationRule`, `LifecycleRule` (constructor-indexed), `fullRule`,
  `globalControlModel`, `globalStep`, `globalTrace`.
* `RegistrationUndo`/`RegistrationResult`/`registrationInverse` and
  `RetireInverseAdequate`/`RegistrationInverseAdequate` (nested-registration
  inverse linkage).
* `printedCaseOf` and the Divert-to-printed-case mapping.
* `withdrawRule`, `iterationRule`, `failureRule` subfamily views with
  guard/frame theorems.
* `commitProjection`/`commitProjection_keys_subset`/`finish_tableConfined`
  (provision-confined finish commit).
* `SelectedBody`/`ControlEdit`/`BodyClass` factorization with ONE resolved
  witness threading both sides, `fullRule_factorizes`; the nonconstant
  fixed-operation replay evidence lives in the fixture.
* Envelope-guarded effectful constructors (iter/finish/divertLand/unload
  with `*Envelope ⊆ provides` guards); `BodyFrameAdequacy` interpreting the
  parameterized provision envelope, the read window, the accumulator
  domain frame, and the strengthened cleanup frame; per-constructor
  `*_full_writeFrame`/`*_full_readNoninterference` discharges,
  `unload_full_cleanupFrame`, `unload_noAllocation`.
* `divertAdmissible` (A.async) with landing-witness and boundary-abort
  theorems.
* `globalStagingModel`, `baseOrchestrationRule`, `baseLifecycleRule`,
  `globalStutterProfile`, `globalAtomicAdequacy` (ADR-08 R.base as genuine
  macro specialization).
* Per-constructor D48 write/read frame discharges (identity bodies and
  control edits), the lifecycle no-allocation/registry-domain theorems, and
  the O-Insert preservation theorems for the static/data-coherence
  conjuncts.
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
  ComponentSemantics Key GState Value Action Iterator Accumulator Flight Failure

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
  | changed (ω : Finmap (fun _ : Key => Name))

/-! ### Labels: operations, never endpoints -/

/-- Orchestration labels name orchestration inputs only: the registrar, the
fresh identity, and the child payload. The retirement cell and the removal
preconditions are rule-local lookup witnesses. -/
inductive GlobalOrchestrationLabel (Name : Type u) (Cell : Type v) where
  | insert (registrar : Option Name) (fresh : Name) (child : Cell)
  | retire (owner : Name)
  | remove (owner : Name)

/-- Lifecycle labels name lifecycle operations only: the target view, the
continuation, the landing token, boundary evidence, and the complete failure
evidence. Success endpoints (the stage/landing results, the accumulator
middle, the launch token) are bound by the rule-local semantic witnesses. -/
inductive GlobalLifecycleLabel (Name : Type u) (Key : Type v) (Iterator : Type w)
    (Flight : Type x) (Failure : Type y) where
  | begin (owner : Name) (ω : Finmap (fun _ : Key => Name))
  | iter (owner : Name) (next : Iterator)
  | finish (owner : Name)
  | divertAbort (owner : Name) (boundary : BoundaryEvidence Key Name)
  | divertLand (owner : Name) (landing : Flight)
  | raise (owner : Name) (failure : Failure)
  | leave (owner : Name)
  | unload (owner : Name)

local notation "OLabel" => GlobalOrchestrationLabel Name GCell
local notation "LLabel" => GlobalLifecycleLabel Name Key Iterator Flight Failure

/-- The printed case of a concrete label. -/
def printedCaseOf : Sum OLabel LLabel → PrintedCase
  | .inl (.insert _ _ _) => .insert
  | .inl (.retire _) => .retire
  | .inl (.remove _) => .remove
  | .inr (.begin _ _) => .begin
  | .inr (.iter _ _) => .iter
  | .inr (.finish _) => .finish
  | .inr (.divertAbort _ _) => .divert
  | .inr (.divertLand _ _) => .divert
  | .inr (.raise _ _) => .raise
  | .inr (.leave _) => .leave
  | .inr (.unload _) => .unload

omit [DecidableEq Name] [DecidableEq Key] in
theorem printedCaseOf_divertAbort (owner : Name) (boundary : BoundaryEvidence Key Name) :
    printedCaseOf (Name := Name) (Key := Key) (Value := Value) (Action := Action)
      (Iterator := Iterator) (Accumulator := Accumulator) (Flight := Flight)
      (Failure := Failure) (.inr (.divertAbort owner boundary : LLabel)) = .divert := rfl

omit [DecidableEq Name] [DecidableEq Key] in
theorem printedCaseOf_divertLand (owner : Name) (landing : Flight) :
    printedCaseOf (Name := Name) (Key := Key) (Value := Value) (Action := Action)
      (Iterator := Iterator) (Accumulator := Accumulator) (Flight := Flight)
      (Failure := Failure) (.inr (.divertLand owner landing : LLabel)) = .divert := rfl

/-- The acting owner of a concrete lifecycle label. -/
def ownerOf : LLabel → Name
  | .begin owner _ => owner
  | .iter owner _ => owner
  | .finish owner => owner
  | .divertAbort owner _ => owner
  | .divertLand owner _ => owner
  | .raise owner _ => owner
  | .leave owner => owner
  | .unload owner => owner

/-! ### Successor equations -/

/-- The pure control edit over one registry cell. -/
def editCell (state : GState) (owner : Name) (edit : GCell → GCell) : GState :=
  { state with registry :=
      match Finmap.lookup owner state.registry with
      | some cell => Finmap.insert owner (edit cell) state.registry
      | none => state.registry }

/-- O-Remove: erase the owner's cell, nothing else. -/
def removeState (state : GState) (owner : Name) : GState :=
  { state with registry := Finmap.erase owner state.registry }

/-- O-Retire: set the retired flag, nothing else. -/
def retireState (state : GState) (owner : Name) : GState :=
  editCell state owner (fun cell => { cell with retired := true })

/-- L-Begin installs the committed target, the root iterator, the identity
accumulator, and exactly the launched pending flight. -/
def beginPayload (sem : GSem) (cell : GCell) (flight : Flight) :=
  { cell.payload with iteratorCode := cell.component.iteratorCode, accumulatorCode := sem.identityAccumulator, flightCode := some flight }

/-- L-Begin: reloading with the committed target view and the launch token. -/
def beginState (sem : GSem) (state : GState) (owner : Name)
    (ω : Finmap (fun _ : Key => Name)) (flight : Flight) : GState :=
  editCell state owner (fun cell =>
    { cell with phase := .reloading, committedView := ω, payload := beginPayload sem cell flight })

/-- L-Iter payload: continuation update; the yielded inverse is composed LIFO —
`composeInverse old new` executes `new` (the current stage) before `old` (the
earlier prefix). -/
def iterPayload (sem : GSem) (cell : GCell) (inverse : Accumulator) (next : Iterator) :=
  { cell.payload with iteratorCode := next, accumulatorCode := sem.composeInverse cell.payload.accumulatorCode inverse }

/-- L-Iter: the stage has already executed; the control edit updates the
continuation and composes the yielded inverse into the accumulator. -/
def iterState (sem : GSem) (state : GState) (owner : Name) (inverse : Accumulator)
    (next : Iterator) : GState :=
  editCell state owner (fun cell =>
    { cell with payload := iterPayload sem cell inverse next })

/-- The committed-table projection: the coeffect store restricted to the
declared provision envelope. A multi-key global store must never be committed
in full — only the acting fiber's provided keys enter its committed table. -/
def commitProjection (state : GState) (provides : Finset Key) :
    Finmap (fun _ : Key => Value) :=
  { entries := state.coeffects.entries.filter (fun entry => entry.1 ∈ provides)
    nodupKeys := by
      exact Quot.inductionOn state.coeffects.entries
        (fun l =>
          List.NodupKeys.sublist
            (List.filter_sublist (p := fun (a : Sigma (fun _ : Key => Value)) =>
              decide (a.1 ∈ provides))))
        state.coeffects.nodupKeys }

/-- The committed-table projection stays inside the declared provision envelope. -/
theorem commitProjection_keys_subset (state : GState) (provides : Finset Key) :
    (commitProjection state provides).keys ⊆ provides := by
  intro key hk
  rw [Finmap.mem_keys] at hk
  rw [Finmap.mem_def] at hk
  change key ∈ Multiset.map Sigma.fst
    (Multiset.filter (fun entry => entry.1 ∈ provides) state.coeffects.entries) at hk
  rw [Multiset.mem_map] at hk
  rcases hk with ⟨entry, hmem, hfst⟩
  rw [Multiset.mem_filter] at hmem
  exact hfst ▸ hmem.2

/-- L-Finish: the stage has already executed; the control edit composes the
final inverse, commits the coeffect store projected to the owner's provision
envelope as the committed table, activates, and clears flight and failure. -/
def finishState (sem : GSem) (state : GState) (owner : Name) (finalInverse : Accumulator) :
    GState :=
  editCell state owner (fun cell =>
    { cell with phase := .active, committed := { entries := commitProjection state cell.component.provides }, payload := { cell.payload with accumulatorCode := sem.composeInverse cell.payload.accumulatorCode finalInverse, flightCode := none, failureData := none } })

/-- The finish control edit's owner-cell equation for a witnessed source cell. -/
theorem finish_lookup_owner (sem : GSem) (state : GState) (owner : Name) (finalInverse : Accumulator)
    {ownerCell : GCell} (hlook : Finmap.lookup owner state.registry = some ownerCell) :
    Finmap.lookup owner (finishState sem state owner finalInverse).registry =
      some { ownerCell with phase := .active, committed := { entries := commitProjection state ownerCell.component.provides }, payload := { ownerCell.payload with accumulatorCode := sem.composeInverse ownerCell.payload.accumulatorCode finalInverse, flightCode := none, failureData := none } } := by
  unfold finishState editCell
  rw [hlook]
  rw [Finmap.lookup_insert]

/-- The finish control edit never touches a foreign cell. -/
theorem finish_lookup_ne (sem : GSem) (state : GState) (owner : Name) (finalInverse : Accumulator)
    {name : Name} (hname : name ≠ owner) :
    Finmap.lookup name (finishState sem state owner finalInverse).registry =
      Finmap.lookup name state.registry := by
  unfold finishState editCell
  cases hlook : Finmap.lookup owner state.registry with
  | none => rfl
  | some _ => exact Finmap.lookup_insert_of_ne (a := owner) (a' := name) (s := state.registry) hname

/-- L-Finish preserves `TableConfined`: the freshly committed table is the
coeffect store projected to the owner's provisions, foreign cells are
unchanged. -/
theorem finish_tableConfined (sem : GSem) (state : GState) (owner : Name)
    (finalInverse : Accumulator) (hbefore : TableConfined state) :
    TableConfined (finishState sem state owner finalInverse) := by
  intro name cell hlook
  by_cases hname : name = owner
  · subst name
    cases hlookOwner : Finmap.lookup owner state.registry with
    | none =>
        have hnone : Finmap.lookup owner (finishState sem state owner finalInverse).registry = none := by
          simp [finishState, editCell, hlookOwner]
        rw [hnone] at hlook
        cases hlook
    | some ownerCell =>
        rw [finish_lookup_owner sem state owner finalInverse hlookOwner] at hlook
        cases hlook with
        | refl =>
            intro key hkey
            change key ∈ (commitProjection state ownerCell.component.provides).keys at hkey
            exact commitProjection_keys_subset state ownerCell.component.provides hkey
  · rw [finish_lookup_ne sem state owner finalInverse hname] at hlook
    exact hbefore name cell hlook

/-- L-DivertAbort: identity body; the control edit enters teardown. -/
def divertAbortState (state : GState) (owner : Name) : GState :=
  editCell state owner (fun cell => { cell with phase := .unloading })

/-- L-DivertLand: the landing has already executed; the control edit composes
the landing inverse, enters teardown, clears the consumed flight, and never
activates. -/
def divertLandState (sem : GSem) (state : GState) (owner : Name) (inverse : Accumulator) :
    GState :=
  editCell state owner (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := sem.composeInverse cell.payload.accumulatorCode inverse, flightCode := none } })

/-- L-Raise: the failure bridge has built the complete retained failure; the
control edit records it and enters teardown, never failing directly. -/
def raiseState (state : GState) (owner : Name) (failure : Failure) : GState :=
  editCell state owner (fun cell =>
    { cell with phase := .unloading, payload := { cell.payload with failureData := some failure } })

/-- L-Leave: the control edit enters teardown. -/
def leaveState (state : GState) (owner : Name) : GState :=
  editCell state owner (fun cell => { cell with phase := .unloading })

/-- L-Unload: the accumulator has already executed; the control edit clears the
committed view and flight and ends in Failed with a complete failure payload,
otherwise normal Inactive. Never erases the cell. -/
def unloadState (state : GState) (owner : Name) : GState :=
  editCell state owner (fun cell =>
    { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } })

/-! ### Registration linkage -/

/-- The canonical registration undo: retire the fresh owner. -/
inductive RegistrationUndo (Name : Type u) where
  | retire (owner : Name)

/-- The registration result: the fresh identity plus its canonical retirement
inverse. -/
structure RegistrationResult (Name : Type u) where
  fresh : Name
  inverse : RegistrationUndo Name

/-- The canonical registration result for `fresh`: its inverse is exactly
`.retire fresh`. -/
def registrationInverse (fresh : Name) : RegistrationResult Name :=
  ⟨fresh, .retire fresh⟩

omit [DecidableEq Name] in
theorem registrationInverse_retires (fresh : Name) :
    (registrationInverse fresh).inverse = .retire fresh := rfl

/-- The interpretation of the canonical retire inverse: an accumulator code is
retire-adequate for `fresh` when running it at any state where `fresh` is
registered retires exactly `fresh`. -/
def RetireInverseAdequate (sem : GSem) (inverse : Accumulator) (fresh : Name) : Prop :=
  ∀ (state : GState) (cell : GCell), Finmap.lookup fresh state.registry = some cell →
    sem.accumulator inverse state = some (retireState state fresh)

/-- The inverse returned by an action token is the canonical retirement inverse
of `fresh` — the bridge a nested-registration witness uses; a generic `Action`
may only claim to be registration through this relation. -/
def RegistrationInverseAdequate (sem : GSem) (action : Action) (fresh : Name) : Prop :=
  ∀ (before : GState) (result : ActionResult GState Accumulator),
    sem.action action before = some result →
      ∃ inverse, result.inverse? = some inverse ∧ RetireInverseAdequate sem inverse fresh

/-! ### Canonical initial cells -/

/-- A canonical fresh insertion: correct identity/registrar/birth, normal
Inactive with no flight or failure, empty committed table and view, and the
component's authorized initial payload. -/
def CanonicalInitialCell (state : GState) (registrar : Option Name) (fresh : Name)
    (cell : GCell) : Prop :=
  cell.incarnation = fresh ∧ cell.parent = registrar ∧
    (match registrar with
     | some parent => Registered state parent
     | none => True) ∧
      cell.birth = nextBirth state ∧ cell.retired = false ∧ cell.phase = .inactive ∧
        cell.committed.entries = ∅ ∧ cell.committedView = ∅ ∧
          cell.payload = { iteratorCode := cell.component.iteratorCode, accumulatorCode := cell.component.accumulatorCode, flightCode := none, failureData := none }

/-- The boundary evidence realizes the divert-abort guard. -/
def boundaryRealizes (state : GState) (owner : Name) (cell : GCell) :
    BoundaryEvidence Key Name → Prop
  | .absent => TargetAbsent state owner
  | .changed ω => cell.committedView ≠ ω ∧ TargetViewAt state owner ω

/-! ### The rule relations -/

/-- The three orchestration constructors. -/
inductive OrchestrationRule : OLabel → GState → GState → Prop where
  | insert {before : GState} {registrar : Option Name} {fresh : Name} {child : GCell} :
      (hfresh : Finmap.lookup fresh before.registry = none) →
      (hledger : fresh ∉ before.ledger.everIssued) →
      (hcanonical : CanonicalInitialCell before registrar fresh child) →
      (hdisjoint : ∀ (name : Name) (cell' : GCell),
        Finmap.lookup name before.registry = some cell' →
          Disjoint child.component.provides cell'.component.provides) →
      OrchestrationRule (.insert registrar fresh child) before (allocate before fresh child)
  | retire {before : GState} {owner : Name} {cell : GCell} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      OrchestrationRule (.retire owner) before (retireState before owner)
  | remove {before : GState} {owner : Name} {cell : GCell} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hretired : cell.retired = true) →
      (hphase : cell.phase = .inactive ∨ cell.phase = .failed) →
      (hnoChild : ∀ (name : Name) (cell' : GCell),
        Finmap.lookup name before.registry = some cell' →
          cell'.parent = some owner → False) →
      OrchestrationRule (.remove owner) before (removeState before owner)

/-- The eight lifecycle constructors over the external stage/landing/
accumulator/failure semantics. -/
inductive LifecycleRule (sem : GSem) : LLabel → GState → GState → Prop where
  | begin {before : GState} {owner : Name} {ω : Finmap (fun _ : Key => Name)}
      {cell : GCell} {flight : Flight} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .inactive) →
      (hretired : cell.retired = false) →
      (hnoFailure : cell.payload.failureData = none) →
      (hnoFlight : cell.payload.flightCode = none) →
      (htarget : TargetViewAt before owner ω) →
      (hlaunch : sem.launch before = some flight) →
      LifecycleRule sem (.begin owner ω) before (beginState sem before owner ω flight)
  | iter {before after : GState} {owner : Name} {next : Iterator} {cell : GCell}
      {inverse : Accumulator} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .reloading) →
      (htarget : TargetViewAt before owner cell.committedView) →
      (hstage : sem.stage cell.payload.iteratorCode before = some (.yield after inverse next)) →
      (hrank : sem.rank next < sem.rank cell.payload.iteratorCode) →
      (henvelope : sem.stageEnvelope cell.payload.iteratorCode ⊆ cell.component.provides) →
      LifecycleRule sem (.iter owner next) before (iterState sem after owner inverse next)
  | finish {before after : GState} {owner : Name} {cell : GCell} {finalInverse : Accumulator} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .reloading) →
      (htarget : TargetViewAt before owner cell.committedView) →
      (hstage : sem.stage cell.payload.iteratorCode before = some (.halt after finalInverse)) →
      (henvelope : sem.stageEnvelope cell.payload.iteratorCode ⊆ cell.component.provides) →
      LifecycleRule sem (.finish owner) before (finishState sem after owner finalInverse)
  | divertAbort {before : GState} {owner : Name} {boundary : BoundaryEvidence Key Name}
      {cell : GCell} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .reloading) →
      (hboundary : boundaryRealizes before owner cell boundary) →
      LifecycleRule sem (.divertAbort owner boundary) before (divertAbortState before owner)
  | divertLand {before after : GState} {owner : Name} {landing : Flight} {cell : GCell}
      {inverse : Accumulator} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .reloading) →
      (htoken : cell.payload.flightCode = some landing) →
      (hchanged : ¬ TargetViewAt before owner cell.committedView) →
      (hland : sem.landing landing before = some (.landed after inverse)) →
      (henvelope : sem.landingEnvelope landing ⊆ cell.component.provides) →
      LifecycleRule sem (.divertLand owner landing) before (divertLandState sem after owner inverse)
  | raise {before : GState} {owner : Name} {cell : GCell} {error : Failure}
      {failure : Failure} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .reloading) →
      (hstage : sem.stage cell.payload.iteratorCode before = some (.raise error)) →
      (hbridge : sem.failureBridge error before cell.payload.accumulatorCode failure) →
      LifecycleRule sem (.raise owner failure) before (raiseState before owner failure)
  | leave {before : GState} {owner : Name} {cell : GCell} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .active) →
      (hchanged : ¬ TargetViewAt before owner cell.committedView) →
      LifecycleRule sem (.leave owner) before (leaveState before owner)
  | unload {before middle : GState} {owner : Name} {cell : GCell} :
      (hlook : Finmap.lookup owner before.registry = some cell) →
      (hphase : cell.phase = .unloading) →
      (hfree : ¬ ∃ dependent, ReliedUpon before dependent owner) →
      (haccumulator : sem.accumulator cell.payload.accumulatorCode before = some middle) →
      (henvelope : sem.accumulatorEnvelope cell.payload.accumulatorCode ⊆ cell.component.provides) →
      LifecycleRule sem (.unload owner) before (unloadState middle owner)

/-- The authoritative O-Retire step realizes exactly the canonical retire
inverse's state transform. -/
theorem retire_successor_equation (state : GState) (owner : Name) (cell : GCell)
    (hlook : Finmap.lookup owner state.registry = some cell) :
    OrchestrationRule (Name := Name) (Key := Key) (Value := Value) (Action := Action)
      (Iterator := Iterator) (Accumulator := Accumulator) (Flight := Flight)
      (Failure := Failure) (Ambient := Ambient) (.retire owner) state (retireState state owner) := by
  exact (OrchestrationRule.retire hlook)


/-! ### The full rule union and its trace view -/

/-- The single authoritative union. -/
def fullRule (sem : GSem) : Sum OLabel LLabel → GState → GState → Prop
  | .inl label, before, after => OrchestrationRule label before after
  | .inr label, before, after => LifecycleRule sem label before after

/-- The authoritative control model. -/
def globalControlModel (sem : GSem) : ControlModel OLabel LLabel GState :=
  { orchestration := OrchestrationRule
    lifecycle := LifecycleRule sem }

/-- One authoritative global step. -/
abbrev globalStep (sem : GSem) :=
  Step (globalControlModel sem).orchestration (globalControlModel sem).lifecycle

/-- Typed traces of authoritative steps. -/
abbrev globalTrace (sem : GSem) :=
  Trace (globalControlModel sem).orchestration (globalControlModel sem).lifecycle

theorem fullRule_inl (sem : GSem) (label : OLabel) (before after : GState) :
    fullRule sem (.inl label) before after ↔ OrchestrationRule label before after := by
  rfl

theorem fullRule_inr (sem : GSem) (label : LLabel) (before after : GState) :
    fullRule sem (.inr label) before after ↔ LifecycleRule sem label before after := by
  rfl

/-! ### Subfamily views -/

/-- R.withdraw: the teardown withdrawal constructors. -/
def withdrawRule (sem : GSem) : LLabel → GState → GState → Prop
  | .leave owner, before, after => LifecycleRule sem (.leave owner) before after
  | .unload owner, before, after => LifecycleRule sem (.unload owner) before after
  | _, _, _ => False

/-- R.iter: the reloading iteration constructors. -/
def iterationRule (sem : GSem) : LLabel → GState → GState → Prop
  | .begin owner ω, before, after => LifecycleRule sem (.begin owner ω) before after
  | .iter owner next, before, after => LifecycleRule sem (.iter owner next) before after
  | .finish owner, before, after => LifecycleRule sem (.finish owner) before after
  | .divertAbort owner boundary, before, after => LifecycleRule sem (.divertAbort owner boundary) before after
  | .divertLand owner landing, before, after => LifecycleRule sem (.divertLand owner landing) before after
  | _, _, _ => False

/-- R.fail: the failure constructor. -/
def failureRule (sem : GSem) : LLabel → GState → GState → Prop
  | .raise owner failure, before, after => LifecycleRule sem (.raise owner failure) before after
  | _, _, _ => False

theorem withdrawRule_subfamily (sem : GSem) (label : LLabel) (before after : GState)
    (h : withdrawRule sem label before after) :
    LifecycleRule sem label before after := by
  cases label with
  | leave owner => exact h
  | unload owner => exact h
  | _ => cases h

theorem iterationRule_subfamily (sem : GSem) (label : LLabel) (before after : GState)
    (h : iterationRule sem label before after) :
    LifecycleRule sem label before after := by
  cases label with
  | begin _ _ => exact h
  | iter _ _ => exact h
  | finish _ => exact h
  | divertAbort _ _ => exact h
  | divertLand _ _ => exact h
  | _ => cases h

theorem failureRule_subfamily (sem : GSem) (label : LLabel) (before after : GState)
    (h : failureRule sem label before after) :
    LifecycleRule sem label before after := by
  cases label with
  | raise _ _ => exact h
  | _ => cases h

/-- Every failure step enters teardown: the successor phase is unloading. -/
theorem failureRule_enters_teardown (sem : GSem) {label : LLabel} {before after : GState}
    {owner : Name} {failure : Failure}
    (h : failureRule sem label before after) (hlabel : label = .raise owner failure) :
    ∃ cell, Finmap.lookup owner after.registry = some cell ∧ cell.phase = .unloading := by
  subst label
  unfold failureRule at h
  cases h with
  | raise hlook _hphase _hstage _hbridge =>
      rw [raiseState]
      unfold editCell
      rw [hlook]
      simp

/-! ### Body classification -/

/-- The three body classes: identity (no external execution), iterator
(stage execution), accumulator (cleanup execution). -/
inductive BodyClass where
  | identity
  | iterator
  | accumulator
  deriving DecidableEq, Repr

/-- The body class of a concrete label. -/
def bodyClassOf : Sum OLabel LLabel → BodyClass
  | .inl _ => .identity
  | .inr (.begin _ _) => .identity
  | .inr (.iter _ _) => .iterator
  | .inr (.finish _) => .iterator
  | .inr (.divertAbort _ _) => .identity
  | .inr (.divertLand _ _) => .iterator
  | .inr (.raise _ _) => .identity
  | .inr (.leave _) => .identity
  | .inr (.unload _) => .accumulator

/-! ### Body-frame adequacy profile -/

/-- Interprets the abstract body-frame relations concretely over `GState`:
the registry relation means the registry value is preserved (stage/landing
bodies), the domain relation means only the registry keys are preserved (the
accumulator may retire recorded children), the allocation relation means
ledger and history are preserved, the provision relation means coeffects
outside the acting envelope are preserved, the observes relation means the
owner's required keys read the same coeffect values, and the accumulator
frame relation means the strengthened D48 cleanup frame. Instances prove
this non-vacuously (see the fixture). -/
structure BodyFrameAdequacy (sem : GSem) : Prop where
  registry_total : ∀ {before after}, sem.registryFrame before after →
    before.registry = after.registry
  allocation_noAllocation : ∀ {before after}, sem.allocationFrame before after →
    after.ledger = before.ledger ∧ after.allocationHistory = before.allocationHistory
  provision_coeffectFrame : ∀ {before after} {provides : Finset Key},
    sem.writesWithinProvision provides before after →
      ∀ key, key ∉ provides → Coeffect.lookup key before.coeffects = Coeffect.lookup key after.coeffects
  observes_readRespect : ∀ {before after}, sem.observes before after →
    ∀ (owner : Name) (key : Key),
      (∃ cell, Finmap.lookup owner before.registry = some cell ∧ key ∈ cell.component.requires) →
        Coeffect.lookup key before.coeffects = Coeffect.lookup key after.coeffects
  accumulator_domain_total : ∀ {before after}, sem.domainFrame before after →
    before.registry.keys = after.registry.keys
  accumulator_cleanupFrame : ∀ {owner code before after},
    sem.accumulator code before = some after →
      sem.accumulatorFrame code before after → CleanupFrame before owner after

/-! ### Frame and confinement theorems -/

/-- The pure control edit preserves the registry keys. -/
theorem editCell_keys {state : GState} {owner : Name} {cell : GCell} {edit : GCell → GCell}
    (hlook : Finmap.lookup owner state.registry = some cell) :
    (editCell state owner edit).registry.keys = state.registry.keys := by
  unfold editCell
  rw [hlook]
  change (Finmap.insert owner (edit cell) state.registry).keys = state.registry.keys
  apply Finset.ext
  intro name
  rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_keys]
  by_cases hname : name = owner
  · subst name
    rw [← Finmap.lookup_isSome, hlook]
    simp
  · simp [hname]

/-- The pure control edit satisfies the D48 write frame. -/
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
      | some _ => intro key _hkey; simp
      | none => trivial
    · unfold editCell
      cases h : Finmap.lookup owner state.registry with
      | none => simp
      | some _ => simp

/-- The pure control edit satisfies the D48 read-noninterference condition. -/
theorem editCell_readNoninterference (state : GState) (owner : Name) (edit : GCell → GCell) :
    ReadNoninterference state owner (editCell state owner edit) := by
  unfold ReadNoninterference
  unfold editCell
  cases h : Finmap.lookup owner state.registry with
  | some _ => intro key _hkey; simp
  | none => trivial

/-- O-Remove satisfies the D48 write frame: it erases only the owner's cell. -/
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

/-- O-Remove satisfies the D48 read-noninterference condition. -/
theorem removeState_readNoninterference (state : GState) {owner : Name} {cell : GCell}
    (hlook : Finmap.lookup owner state.registry = some cell) :
    ReadNoninterference state owner (removeState state owner) := by
  unfold ReadNoninterference
  rw [hlook]
  intro key _hkey
  simp [removeState]

/-- O-Insert satisfies the D48 registration frame. -/
theorem insert_registrationFrame {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after) :
    RegistrationFrame before fresh child after := by
  cases h with
  | insert hfresh hledger _hcanonical _hdisjoint =>
      exact allocate_registrationFrame before hfresh hledger

/-- O-Insert satisfies the D48 read-noninterference condition relative to the
fresh name. -/
theorem insert_readNoninterference {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after) :
    ReadNoninterference before fresh after := by
  cases h with
  | insert hfresh _hledger _hcanonical _hdisjoint =>
      unfold ReadNoninterference
      rw [hfresh]
      trivial

/-- O-Retire satisfies the D48 write frame. -/
theorem retire_writeFrame {before after : GState} {owner : Name}
    (h : OrchestrationRule (.retire owner) before after) :
    WriteFrame before owner after := by
  cases h with
  | retire _hlook =>
      rw [retireState]
      exact editCell_writeFrame before owner _

/-- O-Retire satisfies the D48 read-noninterference condition. -/
theorem retire_readNoninterference {before after : GState} {owner : Name}
    (h : OrchestrationRule (.retire owner) before after) :
    ReadNoninterference before owner after := by
  cases h with
  | retire _hlook =>
      rw [retireState]
      exact editCell_readNoninterference before owner _

/-- O-Remove satisfies the D48 write frame. -/
theorem remove_writeFrame {before after : GState} {owner : Name}
    (h : OrchestrationRule (.remove owner) before after) :
    WriteFrame before owner after := by
  cases h with
  | remove hlook _hretired _hphase _hnoChild =>
      rw [removeState]
      exact removeState_writeFrame before hlook

/-- O-Remove satisfies the D48 read-noninterference condition. -/
theorem remove_readNoninterference {before after : GState} {owner : Name}
    (h : OrchestrationRule (.remove owner) before after) :
    ReadNoninterference before owner after := by
  cases h with
  | remove hlook _hretired _hphase _hnoChild =>
      rw [removeState]
      exact removeState_readNoninterference before hlook

/-- Every identity-body lifecycle constructor satisfies the D48 write frame
relative to its selected owner. -/
theorem lifecycle_writeFrame (sem : GSem) {label : LLabel} {before after : GState}
    (h : LifecycleRule sem label before after)
    (hbody : bodyClassOf (Value := Value) (Action := Action) (Accumulator := Accumulator)
      (.inr label) = .identity) :
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
    (hbody : bodyClassOf (Value := Value) (Action := Action) (Accumulator := Accumulator)
      (.inr label) = .identity) :
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
theorem finish_controlEdit_writeFrame (sem : GSem) (state : GState) (owner : Name)
    (finalInverse : Accumulator) :
    WriteFrame state owner (finishState sem state owner finalInverse) := by
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
    | some _ => simp

/-- The D48 teardown frame composes: a recorded-child retirement followed by
another retirement of the same cell is impossible (the flag is already set),
so body and control edit chain into one cleanup frame. -/
theorem cleanupFrame_trans {before middle after : GState} {owner : Name}
    (hbody : CleanupFrame before owner middle) (hedit : CleanupFrame middle owner after) :
    CleanupFrame before owner after := by
  unfold CleanupFrame at hbody hedit ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro name hne
    have hb := hbody.1 name hne
    have he := hedit.1 name hne
    rcases hb with hb | hb
    · rcases he with he | he
      · left
        exact hb.trans he
      · rcases he with ⟨cell, hlookm, hret, hparent, hlooka⟩
        right
        refine ⟨cell, ?_, hret, hparent, ?_⟩
        · rw [hb]
          exact hlookm
        · exact hlooka
    · rcases he with he | he
      · right
        rcases hb with ⟨cell, hlookb, hret, hparent, hlookm⟩
        refine ⟨cell, hlookb, hret, hparent, ?_⟩
        · rw [← he]
          exact hlookm
      · rcases hb with ⟨cell, hlookb, _hret, _hparent, hlookm⟩
        rcases he with ⟨cell', hlookm', hret', _hparent', _hlooka⟩
        have hcell' : cell' = { cell with retired := true } :=
          (Option.some.inj (hlookm ▸ hlookm')).symm
        rw [hcell'] at hret'
        cases hret'
  · exact hbody.2.1.trans hedit.2.1
  · exact hbody.2.2.1.trans hedit.2.2.1
  · exact hbody.2.2.2.trans hedit.2.2.2

/-- The full lifecycle step satisfies the D48 write frame when the body-frame
adequacy profile holds: the body preserves the registry and writes within the
acting provision envelope (which the rule guard confines to the owner's
provisions), the control edit writes only the owner cell. -/
theorem bodyEdit_writeFrame (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {before middle after : GState} {owner : Name} {cell : GCell} {provides : Finset Key}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hreg : sem.registryFrame before middle)
    (hprov : sem.writesWithinProvision provides before middle)
    (henvelope : provides ⊆ cell.component.provides)
    (halloc : sem.allocationFrame before middle)
    (hedit : WriteFrame middle owner after) :
    WriteFrame before owner after := by
  have hreg' : before.registry = middle.registry := hadq.registry_total hreg
  have ⟨hled, hhist⟩ := hadq.allocation_noAllocation halloc
  unfold WriteFrame
  constructor
  · intro name hne
    have h1 : Finmap.lookup name before.registry = Finmap.lookup name middle.registry := by
      rw [hreg']
    exact h1.trans (hedit.1 name hne)
  · constructor
    · rw [hlook]
      intro key hkey
      have hcoef := hadq.provision_coeffectFrame hprov key (by intro hmem; exact hkey (henvelope hmem))
      have hlookM : Finmap.lookup owner middle.registry = some cell := by
        rw [← hreg']
        exact hlook
      have hmid : Coeffect.lookup key middle.coeffects = Coeffect.lookup key after.coeffects := by
        simp [WriteFrame, hlookM] at hedit
        exact hedit.2.1 key hkey
      exact hcoef.trans hmid
    · exact ⟨hled.symm.trans hedit.2.2.1, hhist.symm.trans hedit.2.2.2⟩

/-- The full iter step satisfies the D48 write frame: the stage body preserves
the registry and writes within the envelope guard's provision set, the control
edit writes only the owner cell. -/
theorem iter_full_writeFrame (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {owner : Name} {next : Iterator} {cell : GCell} {inverse : Accumulator}
    {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hstage : sem.stage cell.payload.iteratorCode before = some (.yield middle inverse next))
    (henvelope : sem.stageEnvelope cell.payload.iteratorCode ⊆ cell.component.provides)
    (hedit : after = iterState sem middle owner inverse next) :
    WriteFrame before owner after := by
  rw [hedit]
  exact bodyEdit_writeFrame sem hadq hlook (sem.stage_registryFrame hstage rfl)
    (sem.stage_writesWithinProvision hstage rfl) henvelope
    (sem.stage_allocationFrame hstage rfl)
    (iter_controlEdit_writeFrame sem middle owner inverse next)

/-- The full finish step satisfies the D48 write frame. -/
theorem finish_full_writeFrame (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {owner : Name} {cell : GCell} {finalInverse : Accumulator}
    {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hstage : sem.stage cell.payload.iteratorCode before = some (.halt middle finalInverse))
    (henvelope : sem.stageEnvelope cell.payload.iteratorCode ⊆ cell.component.provides)
    (hedit : after = finishState sem middle owner finalInverse) :
    WriteFrame before owner after := by
  rw [hedit]
  exact bodyEdit_writeFrame sem hadq hlook (sem.stage_registryFrame hstage rfl)
    (sem.stage_writesWithinProvision hstage rfl) henvelope
    (sem.stage_allocationFrame hstage rfl)
    (finish_controlEdit_writeFrame sem middle owner finalInverse)

/-- The full divertLand step satisfies the D48 write frame. -/
theorem divertLand_full_writeFrame (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {owner : Name} {landing : Flight} {cell : GCell} {inverse : Accumulator}
    {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hland : sem.landing landing before = some (.landed middle inverse))
    (henvelope : sem.landingEnvelope landing ⊆ cell.component.provides)
    (hedit : after = divertLandState sem middle owner inverse) :
    WriteFrame before owner after := by
  rw [hedit]
  exact bodyEdit_writeFrame sem hadq hlook (sem.landing_registryFrame hland rfl)
    (sem.landing_writesWithinProvision hland rfl) henvelope
    (sem.landing_allocationFrame hland rfl)
    (divertLand_controlEdit_writeFrame sem middle owner inverse)

/-- The full unload step satisfies the D48 teardown frame: the accumulator body
fulfills the strengthened cleanup frame (foreign edits are recorded-child
retirements only) and the control edit writes only the owner cell.  The
unload body may retire recorded children, so no full write frame is claimed. -/
theorem unload_full_cleanupFrame (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {owner : Name} {before middle after : GState}
    (haccumulator : ∃ cell : GCell,
      sem.accumulator cell.payload.accumulatorCode before = some middle)
    (hedit : after = unloadState middle owner) :
    CleanupFrame before owner after := by
  rcases haccumulator with ⟨cell, hacc⟩
  rw [hedit]
  exact cleanupFrame_trans (hadq.accumulator_cleanupFrame hacc (sem.accumulator_frame hacc))
    (unload_controlEdit_cleanupFrame middle owner)

/-- The pure control edit never touches the coeffect store. -/
theorem editCell_coeffects (state : GState) (owner : Name) (edit : GCell → GCell) :
    ∀ key, Coeffect.lookup key (editCell state owner edit).coeffects =
      Coeffect.lookup key state.coeffects := by
  intro key
  rfl

/-- The body-edit chain preserves the D48 read window: the body observes the
owner's required keys and the control edit never touches coeffects. -/
theorem bodyEdit_readNoninterference (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {before middle after : GState} {owner : Name} {cell : GCell}
    (hobs : sem.observes before middle)
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hcoef : ∀ key, Coeffect.lookup key middle.coeffects = Coeffect.lookup key after.coeffects) :
    ReadNoninterference before owner after := by
  unfold ReadNoninterference
  rw [hlook]
  intro key hkey
  have hobs' := hadq.observes_readRespect hobs owner key ⟨cell, hlook, hkey⟩
  exact hobs'.trans (hcoef key)

/-- The full iter step preserves the D48 read window: the stage body observes
the owner's required keys, the control edit never touches coeffects. -/
theorem iter_full_readNoninterference (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {owner : Name} {next : Iterator} {cell : GCell} {inverse : Accumulator}
    {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hstage : sem.stage cell.payload.iteratorCode before = some (.yield middle inverse next))
    (hedit : after = iterState sem middle owner inverse next) :
    ReadNoninterference before owner after := by
  rw [hedit]
  exact bodyEdit_readNoninterference sem hadq (sem.stage_frame hstage rfl) hlook
    (by intro key; exact (editCell_coeffects middle owner
      (fun cell => { cell with payload := iterPayload sem cell inverse next }) key).symm)

/-- The full finish step preserves the D48 read window. -/
theorem finish_full_readNoninterference (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {owner : Name} {cell : GCell} {finalInverse : Accumulator}
    {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hstage : sem.stage cell.payload.iteratorCode before = some (.halt middle finalInverse))
    (hedit : after = finishState sem middle owner finalInverse) :
    ReadNoninterference before owner after := by
  rw [hedit]
  exact bodyEdit_readNoninterference sem hadq (sem.stage_frame hstage rfl) hlook
    (by intro key; exact (editCell_coeffects middle owner
      (fun cell => { cell with phase := .active, committed := { entries := commitProjection middle cell.component.provides }, payload := { cell.payload with accumulatorCode := sem.composeInverse cell.payload.accumulatorCode finalInverse, flightCode := none, failureData := none } }) key).symm)

/-- The full divertLand step preserves the D48 read window. -/
theorem divertLand_full_readNoninterference (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {owner : Name} {landing : Flight} {cell : GCell} {inverse : Accumulator}
    {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hland : sem.landing landing before = some (.landed middle inverse))
    (hedit : after = divertLandState sem middle owner inverse) :
    ReadNoninterference before owner after := by
  rw [hedit]
  exact bodyEdit_readNoninterference sem hadq (sem.landing_frame hland rfl) hlook
    (by intro key; exact (editCell_coeffects middle owner
      (fun cell => { cell with phase := .unloading, payload := { cell.payload with accumulatorCode := sem.composeInverse cell.payload.accumulatorCode inverse, flightCode := none } }) key).symm)

/-- The full unload step preserves the D48 read window: the accumulator body
observes the owner's required keys (the cleanup frame holds the coeffect store
fixed in particular), the control edit never touches coeffects. -/
theorem unload_full_readNoninterference (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {owner : Name} {cell : GCell} {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (haccumulator : sem.accumulator cell.payload.accumulatorCode before = some middle)
    (hedit : after = unloadState middle owner) :
    ReadNoninterference before owner after := by
  rw [hedit]
  exact bodyEdit_readNoninterference sem hadq (sem.accumulator_observes haccumulator) hlook
    (by intro key; exact (editCell_coeffects middle owner
      (fun cell => { cell with phase := (if cell.payload.failureData.isSome then .failed else .inactive), committedView := ∅, payload := { cell.payload with flightCode := none } }) key).symm)

/-- The unload step never allocates a name: the accumulator body preserves the
registry keys (domain frame — it may still retire recorded children) and the
ledger/history, and the control edit erases nothing. -/
theorem unload_noAllocation (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {before middle : GState} {owner : Name} {cell : GCell}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (_hphase : cell.phase = .unloading)
    (_hfree : ¬ ∃ dependent, ReliedUpon before dependent owner)
    (haccumulator : sem.accumulator cell.payload.accumulatorCode before = some middle)
    (_henvelope : sem.accumulatorEnvelope cell.payload.accumulatorCode ⊆ cell.component.provides) :
    (unloadState middle owner).registry.keys = before.registry.keys ∧
      (unloadState middle owner).ledger = before.ledger ∧
        (unloadState middle owner).allocationHistory = before.allocationHistory := by
  have hkeys := (hadq.accumulator_domain_total (sem.accumulator_domainFrame haccumulator)).symm
  have hledger := (hadq.allocation_noAllocation (sem.accumulator_allocationFrame haccumulator)).1
  have hhistory := (hadq.allocation_noAllocation (sem.accumulator_allocationFrame haccumulator)).2
  have hmemMid : owner ∈ middle.registry.keys := by
    rw [hkeys]
    rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hlook]
    rfl
  have hlookMid : ∃ cell, Finmap.lookup owner middle.registry = some cell :=
    Finmap.mem_iff.mp hmemMid
  rcases hlookMid with ⟨cell', hlookMid⟩
  unfold unloadState
  rw [editCell_keys hlookMid]
  unfold editCell
  rw [hlookMid]
  simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hkeys]
  · exact hledger
  · exact hhistory

/-- Identity-body lifecycle rules never allocate a name: the registry domain,
the ledger, and the allocation history are unchanged. -/
theorem lifecycle_noAllocation (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {label : LLabel} {before after : GState}
    (h : LifecycleRule sem label before after) :
    after.registry.keys = before.registry.keys ∧ after.ledger = before.ledger ∧
      after.allocationHistory = before.allocationHistory := by
  cases h with
  | begin hlook _hphase _hretired _hnoFailure _hnoFlight _htarget _hlaunch =>
      rw [beginState, editCell_keys hlook]
      unfold editCell
      rw [hlook]
      simp
  | iter hlook _hphase _htarget hstage _hrank _henvelope =>
      have hreg := (hadq.registry_total (sem.stage_registryFrame hstage rfl)).symm
      have hledger := (hadq.allocation_noAllocation (sem.stage_allocationFrame hstage rfl)).1
      have hhistory := (hadq.allocation_noAllocation (sem.stage_allocationFrame hstage rfl)).2
      have hlookAfter : ∃ cell, Finmap.lookup _ _ = some cell := ⟨_, hreg ▸ hlook⟩
      rcases hlookAfter with ⟨cell, hlookAfter⟩
      unfold iterState
      rw [editCell_keys hlookAfter]
      unfold editCell
      rw [hlookAfter]
      simp
      refine ⟨?_, ?_, ?_⟩
      · rw [hreg]
      · exact hledger
      · exact hhistory
  | finish hlook _hphase _htarget hstage _henvelope =>
      have hreg := (hadq.registry_total (sem.stage_registryFrame hstage rfl)).symm
      have hledger := (hadq.allocation_noAllocation (sem.stage_allocationFrame hstage rfl)).1
      have hhistory := (hadq.allocation_noAllocation (sem.stage_allocationFrame hstage rfl)).2
      have hlookAfter : ∃ cell, Finmap.lookup _ _ = some cell := ⟨_, hreg ▸ hlook⟩
      rcases hlookAfter with ⟨cell, hlookAfter⟩
      unfold finishState
      rw [editCell_keys hlookAfter]
      unfold editCell
      rw [hlookAfter]
      simp
      refine ⟨?_, ?_, ?_⟩
      · rw [hreg]
      · exact hledger
      · exact hhistory
  | divertAbort hlook _hphase _hboundary =>
      rw [divertAbortState, editCell_keys hlook]
      unfold editCell
      rw [hlook]
      simp
  | divertLand hlook _hphase _htoken _hchanged hland _henvelope =>
      have hreg := (hadq.registry_total (sem.landing_registryFrame hland rfl)).symm
      have hledger := (hadq.allocation_noAllocation (sem.landing_allocationFrame hland rfl)).1
      have hhistory := (hadq.allocation_noAllocation (sem.landing_allocationFrame hland rfl)).2
      have hlookAfter : ∃ cell, Finmap.lookup _ _ = some cell := ⟨_, hreg ▸ hlook⟩
      rcases hlookAfter with ⟨cell, hlookAfter⟩
      unfold divertLandState
      rw [editCell_keys hlookAfter]
      unfold editCell
      rw [hlookAfter]
      simp
      refine ⟨?_, ?_, ?_⟩
      · rw [hreg]
      · exact hledger
      · exact hhistory
  | raise hlook _hphase _hstage _hbridge =>
      rw [raiseState, editCell_keys hlook]
      unfold editCell
      rw [hlook]
      simp
  | leave hlook _hphase _hchanged =>
      rw [leaveState, editCell_keys hlook]
      unfold editCell
      rw [hlook]
      simp
  | unload hlook _hphase _hfree haccumulator _henvelope =>
      simpa using (unload_noAllocation sem hadq hlook _hphase _hfree haccumulator _henvelope)

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
      refine ⟨?_, ?_, ?_⟩
      · apply Finset.ext
        intro name
        rw [Finmap.mem_keys, Finmap.mem_insert, Finmap.mem_keys]
        by_cases hname : name = owner
        · subst name
          rw [← Finmap.lookup_isSome, h]
          simp
        · simp [hname]
      · rfl
      · rfl

/-! ### O-Insert preserves the static/data-coherence conjuncts -/

/-- O-Insert preserves `TableConfined`: the fresh canonical cell has an empty
committed table, foreign cells are unchanged. -/
theorem insert_tableConfined {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : TableConfined before) : TableConfined after := by
  rcases h with ⟨hfresh, _hledger, hcanonical, _hdisjoint⟩
  intro name cell hlook
  by_cases hname : name = fresh
  · subst name
    rw [allocate_lookup_fresh] at hlook
    cases hlook with
    | refl =>
        have hempty : child.committed.entries = ∅ := hcanonical.2.2.2.2.2.2.1
        rw [hempty]
        simp
  · rw [allocate_lookup_ne before fresh child hname] at hlook
    exact hbefore name cell hlook

/-- O-Insert preserves `ProvisionDisjoint`: the fresh cell is disjoint from all
registered provisions by the rule guard. -/
theorem insert_provisionDisjoint {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : ProvisionDisjoint before) : ProvisionDisjoint after := by
  rcases h with ⟨hfresh, _hledger, _hcanonical, hdisjoint⟩
  intro a b ca cb ha hb hab
  by_cases ha' : a = fresh
  · subst a
    rw [allocate_lookup_fresh] at ha
    cases ha with
    | refl =>
        by_cases hb' : b = fresh
        · subst b
          rw [allocate_lookup_fresh] at hb
          cases hb with
          | refl => exact (hab rfl).elim
        · rw [allocate_lookup_ne before fresh child hb'] at hb
          exact hdisjoint b cb hb
  · rw [allocate_lookup_ne before fresh child ha'] at ha
    by_cases hb' : b = fresh
    · subst b
      rw [allocate_lookup_fresh] at hb
      cases hb with
      | refl =>
          have hsym := hdisjoint a ca ha
          exact Disjoint.symm hsym
    · rw [allocate_lookup_ne before fresh child hb'] at hb
      exact hbefore ha hb hab

/-- O-Insert preserves `CommittedViewClosed`: the fresh canonical cell has an
empty committed view. -/
theorem insert_committedViewClosed {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : CommittedViewClosed before) : CommittedViewClosed after := by
  rcases h with ⟨hfresh, _hledger, hcanonical, _hdisjoint⟩
  intro name cell hlook key provider hkv
  by_cases hname : name = fresh
  · subst name
    rw [allocate_lookup_fresh] at hlook
    cases hlook with
    | refl =>
        have hview : child.committedView = ∅ := hcanonical.2.2.2.2.2.2.2.1
        rw [hview, Finmap.lookup_empty] at hkv
        cases hkv
  · rw [allocate_lookup_ne before fresh child hname] at hlook
    rw [allocate_keys]
    exact Finset.mem_insert.mpr (Or.inr (hbefore name cell hlook key provider hkv))

/-- O-Insert preserves `CommittedProvidersClosed`. -/
theorem insert_committedProvidersClosed {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : CommittedProvidersClosed before) : CommittedProvidersClosed after := by
  rcases h with ⟨hfresh, _hledger, hcanonical, _hdisjoint⟩
  intro name cell hlook key provider hkv
  by_cases hname : name = fresh
  · subst name
    rw [allocate_lookup_fresh] at hlook
    cases hlook with
    | refl =>
        have hview : child.committedView = ∅ := hcanonical.2.2.2.2.2.2.2.1
        rw [hview, Finmap.lookup_empty] at hkv
        cases hkv
  · rw [allocate_lookup_ne before fresh child hname] at hlook
    rcases hbefore name cell hlook key provider hkv with ⟨fiber, hlookp, hkeys, hphase⟩
    have hprov : provider ≠ fresh := by
      intro hprov
      subst provider
      have hbad : none = some fiber := by simp [hfresh] at hlookp
      cases hbad
    refine ⟨fiber, ?_, hkeys, hphase⟩
    rw [allocate_lookup_ne before fresh child hprov]
    exact hlookp

/-- O-Insert preserves `IncarnationCoherent`: the fresh identity is canonical. -/
theorem insert_incarnationCoherent {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : IncarnationCoherent before) : IncarnationCoherent after := by
  rcases h with ⟨hfresh, _hledger, hcanonical, _hdisjoint⟩
  intro name cell hlook
  by_cases hname : name = fresh
  · subst name
    rw [allocate_lookup_fresh] at hlook
    cases hlook with
    | refl => exact hcanonical.1
  · rw [allocate_lookup_ne before fresh child hname] at hlook
    exact hbefore name cell hlook

/-- O-Insert preserves `ParentClosed`: the registrar is registered, the fresh
parent points at it or is the root. -/
theorem insert_parentClosed {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : ParentClosed before) : ParentClosed after := by
  rcases h with ⟨hfresh, _hledger, hcanonical, _hdisjoint⟩
  intro name cell hlook
  by_cases hname : name = fresh
  · subst name
    rw [allocate_lookup_fresh] at hlook
    cases hlook with
    | refl =>
        cases registrar with
        | none => rw [hcanonical.2.1]; trivial
        | some parent =>
            rw [hcanonical.2.1]
            change parent ∈ (allocate before fresh child).registry.keys
            rw [allocate_keys, Finset.mem_insert]
            right
            rw [Finmap.mem_keys, ← Finmap.lookup_isSome]
            rcases hcanonical.2.2.1 with ⟨_fiber, hlookp⟩
            rw [hlookp]
            rfl
  · rw [allocate_lookup_ne before fresh child hname] at hlook
    have hbefore' := hbefore name cell hlook
    -- the foreign parent is in the before keys, hence in the after keys
    cases hparent : cell.parent with
    | none => trivial
    | some parent =>
        change parent ∈ (allocate before fresh child).registry.keys
        rw [allocate_keys, Finset.mem_insert]
        right
        simpa [hparent] using hbefore'

/-- O-Insert preserves `AllocationCoherent`, given ledger coherence for the
freshness of the history. -/
theorem insert_allocationCoherent {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : AllocationCoherent before) (hledgerBefore : LedgerCoherent before) :
    AllocationCoherent after := by
  rcases h with ⟨hfresh, hledger, hcanonical, _hdisjoint⟩
  constructor
  · -- history Nodup: fresh is new (fresh ∉ everIssued, history ⊆ everIssued)
    have hnotin : fresh ∉ before.allocationHistory := by
      intro hmem
      exact hledger (hledgerBefore.2 fresh hmem)
    rw [allocate]
    exact List.nodup_append.mpr ⟨hbefore.1, ⟨List.nodup_singleton _,
      by intro a ha b hb
         have hb' : b = fresh := List.mem_singleton.mp hb
         subst b
         intro h
         exact hnotin (h ▸ ha)⟩⟩
  · intro name cell hlook
    by_cases hname : name = fresh
    · subst name
      rw [allocate_lookup_fresh] at hlook
      cases hlook with
      | refl =>
          constructor
          · rw [allocate, hcanonical.2.2.2.1]
            unfold nextBirth
            rw [List.length_append]
            simp
          · rw [allocate, hcanonical.2.2.2.1]
            change (before.allocationHistory ++ [fresh])[before.allocationHistory.length]? = some fresh
            rw [List.getElem?_append_right (by omega)]
            simp
    · rw [allocate_lookup_ne before fresh child hname] at hlook
      rcases hbefore.2 name cell hlook with ⟨hbirth, hlookup⟩
      constructor
      · rw [allocate]
        simpa [List.length_append] using Nat.lt_trans hbirth (Nat.lt_succ_self _)
      · rw [allocate]
        rw [List.getElem?_append_left hbirth]
        exact hlookup

/-- O-Insert preserves `LedgerCoherent`. -/
theorem insert_ledgerCoherent {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : LedgerCoherent before) : LedgerCoherent after := by
  rcases h with ⟨hfresh, hledger, _hcanonical, _hdisjoint⟩
  constructor
  · intro name hmem
    change name ∈ (Finmap.insert fresh child before.registry).keys at hmem
    rw [Finmap.mem_keys, Finmap.mem_insert] at hmem
    rcases hmem with hmem | hmem
    · subst name
      change fresh ∈ insert fresh before.ledger.everIssued
      simp
    · exact Finset.mem_insert.mpr (Or.inr (hbefore.1 hmem))
  · intro name hmem
    change name ∈ before.allocationHistory ++ [fresh] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact Finset.mem_insert.mpr (Or.inr (hbefore.2 name hmem))
    · have hname : name = fresh := List.mem_singleton.mp hmem
      subst name
      change fresh ∈ insert fresh before.ledger.everIssued
      simp

/-- O-Insert preserves `ActiveTableCoherent`: the fresh canonical cell is
inactive with an empty table. -/
theorem insert_activeTableCoherent {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : ActiveTableCoherent before) : ActiveTableCoherent after := by
  rcases h with ⟨hfresh, _hledger, hcanonical, _hdisjoint⟩
  intro name cell hlook hactive
  by_cases hname : name = fresh
  · subst name
    rw [allocate_lookup_fresh] at hlook
    cases hlook with
    | refl =>
        rw [hcanonical.2.2.2.2.2.1] at hactive
        cases hactive
  · rw [allocate_lookup_ne before fresh child hname] at hlook
    exact hbefore name cell hlook hactive

/-- O-Insert preserves `CommittedViewDomain`: the fresh canonical cell has an
empty committed view. -/
theorem insert_committedViewDomain {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : CommittedViewDomain before) : CommittedViewDomain after := by
  rcases h with ⟨hfresh, _hledger, hcanonical, _hdisjoint⟩
  intro name cell hlook key hmem
  by_cases hname : name = fresh
  · subst name
    rw [allocate_lookup_fresh] at hlook
    cases hlook with
    | refl =>
        have hview : child.committedView = ∅ := hcanonical.2.2.2.2.2.2.2.1
        rw [hview] at hmem
        simp at hmem
  · rw [allocate_lookup_ne before fresh child hname] at hlook
    exact hbefore name cell hlook hmem

/-- O-Insert preserves the bundled data-coherence invariant. -/
theorem insert_dataCoherent {before after : GState} {registrar : Option Name}
    {fresh : Name} {child : GCell}
    (h : OrchestrationRule (.insert registrar fresh child) before after)
    (hbefore : DataCoherent before) : DataCoherent after := by
  unfold DataCoherent at hbefore ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact insert_activeTableCoherent h hbefore.1
  · exact insert_committedViewDomain h hbefore.2.1
  · exact insert_incarnationCoherent h hbefore.2.2.1
  · exact insert_allocationCoherent h hbefore.2.2.2.1 hbefore.2.2.2.2
  · exact insert_ledgerCoherent h hbefore.2.2.2.2

/-! ### Factorization into selected body and control edit -/

/-- The selected body: guards at the source plus the external execution,
with ONE resolved witness (the middle state and the produced inverse)
threading into the control edit. -/
def SelectedBody (sem : GSem) : Sum OLabel LLabel → GState → GState → Accumulator → Prop
  | .inl (.insert registrar fresh child), before, middle, _ =>
      middle = before ∧ Finmap.lookup fresh before.registry = none ∧
        fresh ∉ before.ledger.everIssued ∧ CanonicalInitialCell before registrar fresh child ∧
          ∀ (name : Name) (cell' : GCell), Finmap.lookup name before.registry = some cell' →
            Disjoint child.component.provides cell'.component.provides
  | .inl (.retire owner), before, middle, _ =>
      middle = before ∧ ∃ cell, Finmap.lookup owner before.registry = some cell
  | .inl (.remove owner), before, middle, _ =>
      middle = before ∧ ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.retired = true ∧ (cell.phase = .inactive ∨ cell.phase = .failed) ∧
          ∀ (name : Name) (cell' : GCell), Finmap.lookup name before.registry = some cell' →
            cell'.parent = some owner → False
  | .inr (.begin owner ω), before, middle, _ =>
      middle = before ∧ ∃ cell flight, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .inactive ∧ cell.retired = false ∧ cell.payload.failureData = none ∧
          cell.payload.flightCode = none ∧ TargetViewAt before owner ω ∧
            sem.launch before = some flight
  | .inr (.iter owner next), before, middle, inverse =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .reloading ∧ TargetViewAt before owner cell.committedView ∧
          sem.stage cell.payload.iteratorCode before = some (.yield middle inverse next) ∧
            sem.rank next < sem.rank cell.payload.iteratorCode ∧
              sem.stageEnvelope cell.payload.iteratorCode ⊆ cell.component.provides
  | .inr (.finish owner), before, middle, finalInverse =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .reloading ∧ TargetViewAt before owner cell.committedView ∧
          sem.stage cell.payload.iteratorCode before = some (.halt middle finalInverse) ∧
            sem.stageEnvelope cell.payload.iteratorCode ⊆ cell.component.provides
  | .inr (.divertAbort owner boundary), before, middle, _ =>
      middle = before ∧ ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .reloading ∧ boundaryRealizes before owner cell boundary
  | .inr (.divertLand owner landing), before, middle, inverse =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .reloading ∧ cell.payload.flightCode = some landing ∧
          ¬ TargetViewAt before owner cell.committedView ∧
            sem.landing landing before = some (.landed middle inverse) ∧
              sem.landingEnvelope landing ⊆ cell.component.provides
  | .inr (.raise owner failure), before, middle, _ =>
      middle = before ∧ ∃ cell error, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .reloading ∧
          sem.stage cell.payload.iteratorCode before = some (.raise error) ∧
            sem.failureBridge error before cell.payload.accumulatorCode failure
  | .inr (.leave owner), before, middle, _ =>
      middle = before ∧ ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .active ∧ ¬ TargetViewAt before owner cell.committedView
  | .inr (.unload owner), before, middle, _ =>
      ∃ cell, Finmap.lookup owner before.registry = some cell ∧
        cell.phase = .unloading ∧ (¬ ∃ dependent, ReliedUpon before dependent owner) ∧
          sem.accumulator cell.payload.accumulatorCode before = some middle ∧
            sem.accumulatorEnvelope cell.payload.accumulatorCode ⊆ cell.component.provides

/-- The control edit: the exact successor equation applied to the body result,
consuming the SAME resolved witness. -/
def ControlEdit (sem : GSem) : Sum OLabel LLabel → GState → Accumulator → GState → Prop
  | .inl (.insert _registrar fresh child), middle, _, after => after = allocate middle fresh child
  | .inl (.retire owner), middle, _, after => after = retireState middle owner
  | .inl (.remove owner), middle, _, after => after = removeState middle owner
  | .inr (.begin owner ω), middle, _, after =>
      ∃ flight, sem.launch middle = some flight ∧ after = beginState sem middle owner ω flight
  | .inr (.iter owner next), middle, inverse, after => after = iterState sem middle owner inverse next
  | .inr (.finish owner), middle, finalInverse, after => after = finishState sem middle owner finalInverse
  | .inr (.divertAbort owner _boundary), middle, _, after => after = divertAbortState middle owner
  | .inr (.divertLand owner _landing), middle, inverse, after => after = divertLandState sem middle owner inverse
  | .inr (.raise owner failure), middle, _, after => after = raiseState middle owner failure
  | .inr (.leave owner), middle, _, after => after = leaveState middle owner
  | .inr (.unload owner), middle, _, after => after = unloadState middle owner

/-- O-Insert factorizes into its canonical body and allocation edit. -/
theorem factor_insert (sem : GSem) {registrar : Option Name} {fresh : Name} {child : GCell}
    {before after : GState} :
    OrchestrationRule (.insert registrar fresh child) before after ↔
      ∃ middle inverse, SelectedBody sem (.inl (.insert registrar fresh child)) before middle inverse ∧
        ControlEdit sem (.inl (.insert registrar fresh child)) middle inverse after := by
  constructor
  · intro h
    rcases h with ⟨hfresh, hledger, hcanonical, hdisjoint⟩
    refine ⟨before, sem.identityAccumulator, ?_, ?_⟩
    · exact ⟨rfl, hfresh, hledger, hcanonical, hdisjoint⟩
    · rfl
  · intro h
    rcases h with ⟨middle, _inverse, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, hfresh, hledger, hcanonical, hdisjoint⟩
    rw [hedit, hmiddle]
    exact OrchestrationRule.insert hfresh hledger hcanonical hdisjoint

/-- O-Retire factorizes into its canonical body and retirement edit. -/
theorem factor_retire (sem : GSem) {owner : Name} {before after : GState} :
    OrchestrationRule (.retire owner) before after ↔
      ∃ middle inverse, SelectedBody sem (.inl (.retire owner)) before middle inverse ∧
        ControlEdit sem (.inl (.retire owner)) middle inverse after := by
  constructor
  · intro h
    cases h with
    | retire hlook =>
        refine ⟨before, sem.identityAccumulator, ?_, ?_⟩
        · exact ⟨rfl, ⟨_, hlook⟩⟩
        · rfl
  · intro h
    rcases h with ⟨middle, _inverse, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, ⟨cell, hlook⟩⟩
    rw [hedit, hmiddle]
    exact OrchestrationRule.retire hlook

/-- O-Remove factorizes into its canonical body and erasure edit. -/
theorem factor_remove (sem : GSem) {owner : Name} {before after : GState} :
    OrchestrationRule (.remove owner) before after ↔
      ∃ middle inverse, SelectedBody sem (.inl (.remove owner)) before middle inverse ∧
        ControlEdit sem (.inl (.remove owner)) middle inverse after := by
  constructor
  · intro h
    cases h with
    | remove hlook hretired hphase hnoChild =>
        refine ⟨before, sem.identityAccumulator, ?_, ?_⟩
        · exact ⟨rfl, ⟨_, hlook, hretired, hphase, hnoChild⟩⟩
        · rfl
  · intro h
    rcases h with ⟨middle, _inverse, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, ⟨cell, hlook, hretired, hphase, hnoChild⟩⟩
    rw [hedit, hmiddle]
    exact OrchestrationRule.remove hlook hretired hphase hnoChild

/-- L-Begin factorizes: the launch witness threads the flight token. -/
theorem factor_begin (sem : GSem) {owner : Name} {ω : Finmap (fun _ : Key => Name)}
    {before after : GState} :
    LifecycleRule sem (.begin owner ω) before after ↔
      ∃ middle inverse, SelectedBody sem (.inr (.begin owner ω)) before middle inverse ∧
        ControlEdit sem (.inr (.begin owner ω)) middle inverse after := by
  constructor
  · intro h
    rcases h with ⟨hlook, hphase, hretired, hnoFailure, hnoFlight, htarget, hlaunch⟩
    refine ⟨before, sem.identityAccumulator, ?_, ?_⟩
    · exact ⟨rfl, ⟨_, _, hlook, hphase, hretired, hnoFailure, hnoFlight, htarget, hlaunch⟩⟩
    · exact ⟨_, hlaunch, rfl⟩
  · intro h
    rcases h with ⟨middle, _inverse, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, ⟨cell, flight, hlook, hphase, hretired, hnoFailure,
      hnoFlight, htarget, hlaunch⟩⟩
    rcases hedit with ⟨flight', hlaunch', hedit'⟩
    rw [hmiddle] at hlaunch'
    have hf : flight = flight' := Option.some.inj (by simpa [hlaunch] using hlaunch')
    subst flight'
    rw [hedit', hmiddle]
    exact LifecycleRule.begin hlook hphase hretired hnoFailure hnoFlight htarget hlaunch

/-- The iter body and edit for one explicitly witnessed stage execution. -/
theorem factor_iter_of (sem : GSem) {owner : Name} {next : Iterator} {cell : GCell}
    {inverse : Accumulator} {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hphase : cell.phase = .reloading)
    (htarget : TargetViewAt before owner cell.committedView)
    (hstage : sem.stage cell.payload.iteratorCode before = some (.yield middle inverse next))
    (hrank : sem.rank next < sem.rank cell.payload.iteratorCode)
    (henvelope : sem.stageEnvelope cell.payload.iteratorCode ⊆ cell.component.provides)
    (hedit : after = iterState sem middle owner inverse next) :
    ∃ middle' inverse', SelectedBody sem (.inr (.iter owner next)) before middle' inverse' ∧
      ControlEdit sem (.inr (.iter owner next)) middle' inverse' after := by
  exact ⟨middle, inverse, ⟨cell, hlook, hphase, htarget, hstage, hrank, henvelope⟩, hedit⟩

/-- L-Iter factorizes with one witness: the stage-produced middle and inverse
are exactly the ones the control edit consumes. -/
theorem factor_iter (sem : GSem) {owner : Name} {next : Iterator} {before after : GState} :
    LifecycleRule sem (.iter owner next) before after ↔
      ∃ middle inverse, SelectedBody sem (.inr (.iter owner next)) before middle inverse ∧
        ControlEdit sem (.inr (.iter owner next)) middle inverse after := by
  constructor
  · intro h
    cases h with
    | iter hlook hphase htarget hstage hrank henvelope =>
        exact factor_iter_of sem hlook hphase htarget hstage hrank henvelope rfl
  · intro h
    rcases h with ⟨middle, inverse, hbody, hedit⟩
    rcases hbody with ⟨cell, hlook, hphase, htarget, hstage, hrank, henvelope⟩
    rw [hedit]
    exact LifecycleRule.iter hlook hphase htarget hstage hrank henvelope
/-- The finish body and edit for one explicitly witnessed halt execution. -/
theorem factor_finish_of (sem : GSem) {owner : Name} {cell : GCell}
    {finalInverse : Accumulator} {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hphase : cell.phase = .reloading)
    (htarget : TargetViewAt before owner cell.committedView)
    (hstage : sem.stage cell.payload.iteratorCode before = some (.halt middle finalInverse))
    (henvelope : sem.stageEnvelope cell.payload.iteratorCode ⊆ cell.component.provides)
    (hedit : after = finishState sem middle owner finalInverse) :
    ∃ middle' finalInverse', SelectedBody sem (.inr (.finish owner)) before middle' finalInverse' ∧
      ControlEdit sem (.inr (.finish owner)) middle' finalInverse' after := by
  exact ⟨middle, finalInverse, ⟨cell, hlook, hphase, htarget, hstage, henvelope⟩, hedit⟩

/-- L-Finish factorizes with one witness: the halt result and the final
inverse thread both sides. -/
theorem factor_finish (sem : GSem) {owner : Name} {before after : GState} :
    LifecycleRule sem (.finish owner) before after ↔
      ∃ middle finalInverse, SelectedBody sem (.inr (.finish owner)) before middle finalInverse ∧
        ControlEdit sem (.inr (.finish owner)) middle finalInverse after := by
  constructor
  · intro h
    cases h with
    | finish hlook hphase htarget hstage henvelope =>
        exact factor_finish_of sem hlook hphase htarget hstage henvelope rfl
  · intro h
    rcases h with ⟨middle, finalInverse, hbody, hedit⟩
    rcases hbody with ⟨cell, hlook, hphase, htarget, hstage, henvelope⟩
    rw [hedit]
    exact LifecycleRule.finish hlook hphase htarget hstage henvelope

/-- L-DivertAbort factorizes into its identity body and teardown edit. -/
theorem factor_divertAbort (sem : GSem) {owner : Name} {boundary : BoundaryEvidence Key Name}
    {before after : GState} :
    LifecycleRule sem (.divertAbort owner boundary) before after ↔
      ∃ middle inverse, SelectedBody sem (.inr (.divertAbort owner boundary)) before middle inverse ∧
        ControlEdit sem (.inr (.divertAbort owner boundary)) middle inverse after := by
  constructor
  · intro h
    cases h with
    | divertAbort hlook hphase hboundary =>
        refine ⟨before, sem.identityAccumulator, ?_, ?_⟩
        · exact ⟨rfl, ⟨_, hlook, hphase, hboundary⟩⟩
        · rfl
  · intro h
    rcases h with ⟨middle, _inverse, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, ⟨cell, hlook, hphase, hboundary⟩⟩
    rw [hedit, hmiddle]
    exact LifecycleRule.divertAbort hlook hphase hboundary

/-- The divertLand body and edit for one explicitly witnessed landing. -/
theorem factor_divertLand_of (sem : GSem) {owner : Name} {landing : Flight} {cell : GCell}
    {inverse : Accumulator} {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hphase : cell.phase = .reloading)
    (htoken : cell.payload.flightCode = some landing)
    (hchanged : ¬ TargetViewAt before owner cell.committedView)
    (hland : sem.landing landing before = some (.landed middle inverse))
    (henvelope : sem.landingEnvelope landing ⊆ cell.component.provides)
    (hedit : after = divertLandState sem middle owner inverse) :
    ∃ middle' inverse', SelectedBody sem (.inr (.divertLand owner landing)) before middle' inverse' ∧
      ControlEdit sem (.inr (.divertLand owner landing)) middle' inverse' after := by
  exact ⟨middle, inverse, ⟨cell, hlook, hphase, htoken, hchanged, hland, henvelope⟩, hedit⟩

/-- L-DivertLand factorizes with one witness: the landed state and the landing
inverse thread both sides. -/
theorem factor_divertLand (sem : GSem) {owner : Name} {landing : Flight}
    {before after : GState} :
    LifecycleRule sem (.divertLand owner landing) before after ↔
      ∃ middle inverse, SelectedBody sem (.inr (.divertLand owner landing)) before middle inverse ∧
        ControlEdit sem (.inr (.divertLand owner landing)) middle inverse after := by
  constructor
  · intro h
    cases h with
    | divertLand hlook hphase htoken hchanged hland henvelope =>
        exact factor_divertLand_of sem hlook hphase htoken hchanged hland henvelope rfl
  · intro h
    rcases h with ⟨middle, inverse, hbody, hedit⟩
    rcases hbody with ⟨cell, hlook, hphase, htoken, hchanged, hland, henvelope⟩
    rw [hedit]
    exact LifecycleRule.divertLand hlook hphase htoken hchanged hland henvelope

/-- L-Raise factorizes into its identity body and failure-recording edit. -/
theorem factor_raise (sem : GSem) {owner : Name} {failure : Failure} {before after : GState} :
    LifecycleRule sem (.raise owner failure) before after ↔
      ∃ middle inverse, SelectedBody sem (.inr (.raise owner failure)) before middle inverse ∧
        ControlEdit sem (.inr (.raise owner failure)) middle inverse after := by
  constructor
  · intro h
    cases h with
    | raise hlook hphase hstage hbridge =>
        refine ⟨before, sem.identityAccumulator, ?_, ?_⟩
        · exact ⟨rfl, ⟨_, _, hlook, hphase, hstage, hbridge⟩⟩
        · rfl
  · intro h
    rcases h with ⟨middle, _inverse, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, ⟨cell, error, hlook, hphase, hstage, hbridge⟩⟩
    rw [hedit, hmiddle]
    exact LifecycleRule.raise hlook hphase hstage hbridge

/-- L-Leave factorizes into its identity body and teardown edit. -/
theorem factor_leave (sem : GSem) {owner : Name} {before after : GState} :
    LifecycleRule sem (.leave owner) before after ↔
      ∃ middle inverse, SelectedBody sem (.inr (.leave owner)) before middle inverse ∧
        ControlEdit sem (.inr (.leave owner)) middle inverse after := by
  constructor
  · intro h
    cases h with
    | leave hlook hphase hchanged =>
        refine ⟨before, sem.identityAccumulator, ?_, ?_⟩
        · exact ⟨rfl, ⟨_, hlook, hphase, hchanged⟩⟩
        · rfl
  · intro h
    rcases h with ⟨middle, _inverse, hbody, hedit⟩
    rcases hbody with ⟨hmiddle, ⟨cell, hlook, hphase, hchanged⟩⟩
    rw [hedit, hmiddle]
    exact LifecycleRule.leave hlook hphase hchanged

/-- The unload body and edit for one explicitly witnessed accumulator run. -/
theorem factor_unload_of (sem : GSem) {owner : Name} {cell : GCell}
    {before middle after : GState}
    (hlook : Finmap.lookup owner before.registry = some cell)
    (hphase : cell.phase = .unloading)
    (hfree : ¬ ∃ dependent, ReliedUpon before dependent owner)
    (haccumulator : sem.accumulator cell.payload.accumulatorCode before = some middle)
    (henvelope : sem.accumulatorEnvelope cell.payload.accumulatorCode ⊆ cell.component.provides)
    (hedit : after = unloadState middle owner) :
    ∃ middle' inverse', SelectedBody sem (.inr (.unload owner)) before middle' inverse' ∧
      ControlEdit sem (.inr (.unload owner)) middle' inverse' after := by
  exact ⟨middle, sem.identityAccumulator, ⟨cell, hlook, hphase, hfree, haccumulator, henvelope⟩, hedit⟩

/-- L-Unload factorizes with one witness: the accumulator middle threads both
sides. -/
theorem factor_unload (sem : GSem) {owner : Name} {before after : GState} :
    LifecycleRule sem (.unload owner) before after ↔
      ∃ middle inverse, SelectedBody sem (.inr (.unload owner)) before middle inverse ∧
        ControlEdit sem (.inr (.unload owner)) middle inverse after := by
  constructor
  · intro h
    cases h with
    | unload hlook hphase hfree haccumulator henvelope =>
        exact factor_unload_of sem hlook hphase hfree haccumulator henvelope rfl
  · intro h
    rcases h with ⟨middle, _inverse, hbody, hedit⟩
    rcases hbody with ⟨cell, hlook, hphase, hfree, haccumulator, henvelope⟩
    rw [hedit]
    exact LifecycleRule.unload hlook hphase hfree haccumulator henvelope

/-- Every authoritative step factorizes into its selected body and control
edit with one resolved witness. -/
theorem fullRule_factorizes (sem : GSem) {label : Sum OLabel LLabel} {before after : GState} :
    fullRule sem label before after ↔
      ∃ middle inverse, SelectedBody sem label before middle inverse ∧
        ControlEdit sem label middle inverse after := by
  cases label with
  | inl l =>
      cases l with
      | insert registrar fresh child => exact factor_insert sem
      | retire owner => exact factor_retire sem
      | remove owner => exact factor_remove sem
  | inr l =>
      cases l with
      | begin owner ω => exact factor_begin sem
      | iter owner next => exact factor_iter sem
      | finish owner => exact factor_finish sem
      | divertAbort owner boundary => exact factor_divertAbort sem
      | divertLand owner landing => exact factor_divertLand sem
      | raise owner failure => exact factor_raise sem
      | leave owner => exact factor_leave sem
      | unload owner => exact factor_unload sem

/-! ### A.async: the asynchronous policy view -/

/-- The async admission of a concrete label at a state, over the frozen
`AsyncPolicy`: a land is admitted when the stored token is landable and the
policy allows `.land`; an abort only at a boundary with the policy's `.abort`
permission. -/
def divertAdmissible (_sem : GSem) (policy : AsyncPolicy Flight GState) :
    Sum OLabel LLabel → GState → Prop
  | .inr (.divertLand owner landing), state =>
      ∃ cell flight, Finmap.lookup owner state.registry = some cell ∧
        cell.payload.flightCode = some flight ∧ flight = landing ∧
          cell.phase = .reloading ∧ policy.allowed flight state .land
  | .inr (.divertAbort owner boundary), state =>
      ∃ cell flight, Finmap.lookup owner state.registry = some cell ∧
        cell.payload.flightCode = some flight ∧ cell.phase = .reloading ∧
          boundaryRealizes state owner cell boundary ∧ policy.allowed flight state .abort
  | _, _ => False

/-- A land rule-step carries its witnessed landing: the stored token's
semantic landing executed with a landed state and an inverse. -/
theorem divertLand_has_landingWitness (sem : GSem) {owner : Name} {landing : Flight}
    {before after : GState}
    (h : LifecycleRule sem (.divertLand owner landing) before after) :
    ∃ landed inverse, sem.landing landing before = some (.landed landed inverse) := by
  cases h with
  | divertLand _hlook _hphase _htoken _hchanged hland =>
      exact ⟨_, _, hland⟩

/-- An admitted abort is at a real boundary. -/
theorem divertAbort_atBoundary (sem : GSem) (policy : AsyncPolicy Flight GState)
    {owner : Name} {boundary : BoundaryEvidence Key Name} {state : GState}
    (hadm : divertAdmissible sem policy (.inr (.divertAbort owner boundary)) state) :
    ∃ cell, Finmap.lookup owner state.registry = some cell ∧
      boundaryRealizes state owner cell boundary := by
  unfold divertAdmissible at hadm
  rcases hadm with ⟨cell, _flight, hlook, _htoken, _hphase, hboundary, _hallowed⟩
  exact ⟨cell, hlook, hboundary⟩

/-- A land step never activates: its successor phase is unloading. -/
theorem divertLand_not_active (sem : GSem) (hadq : BodyFrameAdequacy sem)
    {owner : Name} {landing : Flight} {before after : GState}
    (h : LifecycleRule sem (.divertLand owner landing) before after) :
    ∃ cell, Finmap.lookup owner after.registry = some cell ∧ cell.phase = .unloading := by
  cases h with
  | divertLand hlook _hphase _htoken _hchanged hland _henvelope =>
      have hreg := hadq.registry_total (sem.landing_registryFrame hland rfl)
      have hlookMid : ∃ cell, Finmap.lookup owner _ = some cell := ⟨_, hreg ▸ hlook⟩
      rcases hlookMid with ⟨cell, hlookMid⟩
      rw [divertLandState]
      unfold editCell
      rw [hlookMid]
      simp

/-- A raise step never fails directly: its successor phase is unloading with
the complete retained failure. -/
theorem raise_not_failed (sem : GSem) {owner : Name} {failure : Failure} {before after : GState}
    (h : LifecycleRule sem (.raise owner failure) before after) :
    ∃ cell, Finmap.lookup owner after.registry = some cell ∧ cell.phase = .unloading ∧
      cell.payload.failureData = some failure := by
  cases h with
  | raise hlook _hphase _hstage _hbridge =>
      rw [raiseState]
      unfold editCell
      rw [hlook]
      simp

/-! ### R.base: the Staging macro view -/

/-- The ADR-08 base lifecycle labels: Reload and Unload only; intermediate
Reloading/Unloading states are not stable base states. -/
inductive BaseLifeLabel (Name : Type u) (Key : Type v) where
  | reload (owner : Name) (ω : Finmap (fun _ : Key => Name))
  | unload (owner : Name)

/-- The ADR-08 base model: base orchestration is the singleton orchestration
macro; base Reload is the Begin·Finish macro path; base Unload is the
Leave·Unload macro path. All carriers share one universe, so the frozen
single-universe `StagingModel` carrier applies. -/
def globalStagingModel (sem : GSem) :
    StagingModel GState GState OLabel OLabel (BaseLifeLabel Name Key) LLabel :=
  { embed := id
    project := fun state => some state
    stable := fun _ => True
    fullOrch := OrchestrationRule
    fullLife := LifecycleRule sem
    expandOrch := fun label => [.inl label]
    expandLife := fun label =>
      match label with
      | .reload owner ω => [.inr (.begin owner ω), .inr (.finish owner)]
      | .unload owner => [.inr (.leave owner), .inr (.unload owner)]
    atomicOrch := fun labels => ∃ label, labels = [.inl label]
    atomicLife := fun labels =>
      (∃ owner ω, labels = [.inr (.begin owner ω), .inr (.finish owner)]) ∨
        (∃ owner, labels = [.inr (.leave owner), .inr (.unload owner)])
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

/-- The Begin·Finish macro path is exactly a reload: one begin step followed
by one finish step. -/
theorem reloadPath_lifecycle (sem : GSem) {before after : GState} {owner : Name}
    {ω : Finmap (fun _ : Key => Name)} :
    Nonempty (MacroPath (globalStagingModel sem)
      [.inr (.begin owner ω), .inr (.finish owner)] before after) →
        ∃ middle, LifecycleRule sem (.begin owner ω) before middle ∧
          LifecycleRule sem (.finish owner) middle after := by
  rintro ⟨path⟩
  rcases path with ⟨trace, hlabels⟩
  cases trace with
  | nil => simp [Trace.labels] at hlabels
  | cons head tail =>
      cases tail with
      | nil => simp [Trace.labels] at hlabels
      | cons head' tail' =>
          cases tail' with
          | nil =>
              cases head with
              | orchestration _ _ => simp [Trace.labels, Step.label] at hlabels
              | lifecycle label hpremise =>
                  cases head' with
                  | orchestration _ _ => simp [Trace.labels, Step.label] at hlabels
                  | lifecycle label' hpremise' =>
                      injection hlabels with hhead hrest
                      injection hrest with htail _
                      have hlabel : label = .begin owner ω := by
                        simpa [Step.label] using hhead
                      have hlabel' : label' = .finish owner := by
                        simpa [Step.label] using htail
                      subst label
                      subst label'
                      exact ⟨_, hpremise, hpremise'⟩
          | cons _ _ => simp [Trace.labels] at hlabels

/-- The Leave·Unload macro path is exactly an unload: one leave step followed
by one unload step. -/
theorem unloadPath_lifecycle (sem : GSem) {before after : GState} {owner : Name} :
    Nonempty (MacroPath (globalStagingModel sem)
      [.inr (.leave owner), .inr (.unload owner)] before after) →
        ∃ middle, LifecycleRule sem (.leave owner) before middle ∧
          LifecycleRule sem (.unload owner) middle after := by
  rintro ⟨path⟩
  rcases path with ⟨trace, hlabels⟩
  cases trace with
  | nil => simp [Trace.labels] at hlabels
  | cons head tail =>
      cases tail with
      | nil => simp [Trace.labels] at hlabels
      | cons head' tail' =>
          cases tail' with
          | nil =>
              cases head with
              | orchestration _ _ => simp [Trace.labels, Step.label] at hlabels
              | lifecycle label hpremise =>
                  cases head' with
                  | orchestration _ _ => simp [Trace.labels, Step.label] at hlabels
                  | lifecycle label' hpremise' =>
                      injection hlabels with hhead hrest
                      injection hrest with htail _
                      have hlabel : label = .leave owner := by
                        simpa [Step.label] using hhead
                      have hlabel' : label' = .unload owner := by
                        simpa [Step.label] using htail
                      subst label
                      subst label'
                      exact ⟨_, hpremise, hpremise'⟩
          | cons _ _ => simp [Trace.labels] at hlabels

/-- A base orchestration step is exactly one full orchestration step. -/
theorem baseOrchestration_iff (sem : GSem) (label : OLabel) (before after : GState) :
    baseOrchestrationRule sem label before after ↔ OrchestrationRule label before after := by
  constructor
  · intro h
    rcases h with ⟨_hatomic, hpath⟩
    exact singletonPath_orchestration sem (by simpa [globalStagingModel] using hpath)
  · intro h
    refine ⟨⟨label, rfl⟩, ?_⟩
    refine ⟨Trace.cons (Step.orchestration label h) Trace.nil, ?_⟩
    rfl

/-- A base Reload step is exactly one begin followed by one finish. -/
theorem baseLife_reload_iff (sem : GSem) (owner : Name) (ω : Finmap (fun _ : Key => Name))
    (before after : GState) :
    baseLifecycleRule sem (.reload owner ω) before after ↔
      ∃ middle, LifecycleRule sem (.begin owner ω) before middle ∧
        LifecycleRule sem (.finish owner) middle after := by
  unfold baseLifecycleRule RbLife AtomicLifeMacro
  constructor
  · intro h
    rcases h with ⟨_hatomic, hpath⟩
    exact reloadPath_lifecycle sem (by simpa [globalStagingModel] using hpath)
  · intro h
    rcases h with ⟨middle, hbegin, hfinish⟩
    refine ⟨Or.inl ⟨owner, ω, rfl⟩, ?_⟩
    refine ⟨Trace.cons (Step.lifecycle (.begin owner ω) hbegin)
        (Trace.cons (Step.lifecycle (.finish owner) hfinish) Trace.nil), ?_⟩
    rfl

/-- A base Unload step is exactly one leave followed by one unload. -/
theorem baseLife_unload_iff (sem : GSem) (owner : Name) (before after : GState) :
    baseLifecycleRule sem (.unload owner) before after ↔
      ∃ middle, LifecycleRule sem (.leave owner) before middle ∧
        LifecycleRule sem (.unload owner) middle after := by
  unfold baseLifecycleRule RbLife AtomicLifeMacro
  constructor
  · intro h
    rcases h with ⟨_hatomic, hpath⟩
    exact unloadPath_lifecycle sem (by simpa [globalStagingModel] using hpath)
  · intro h
    rcases h with ⟨middle, hleave, hunload⟩
    refine ⟨Or.inr ⟨owner, rfl⟩, ?_⟩
    refine ⟨Trace.cons (Step.lifecycle (.leave owner) hleave)
        (Trace.cons (Step.lifecycle (.unload owner) hunload) Trace.nil), ?_⟩
    rfl

/-- The profile-tagged stutter permission: orchestration never stutters; a
lifecycle stutter must be a real iter self-loop (the only admitted stutter),
and the adequacy theorem additionally requires the projected base observation
to be unchanged. -/
def globalStutterProfile (sem : GSem) : StutterProfile (globalStagingModel sem) :=
  { Tag := LLabel
    orchestration := fun _tag _labels _before => False
    lifecycle := fun tag labels before =>
      labels = [.inr tag] ∧ (∃ owner next, tag = .iter owner next) ∧
        LifecycleRule sem tag before before }

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
  rcases hatomic with hreload | hunload
  · rcases hreload with ⟨owner, ω, hlabels⟩
    right
    refine ⟨.reload owner ω, ?_, ?_⟩
    · simpa [globalStagingModel] using hlabels
    · exact (baseLife_reload_iff sem owner ω before after).mpr
        (reloadPath_lifecycle sem (by
          rw [hlabels] at path
          exact ⟨path⟩))
  · rcases hunload with ⟨owner, hlabels⟩
    right
    refine ⟨.unload owner, ?_, ?_⟩
    · simpa [globalStagingModel] using hlabels
    · exact (baseLife_unload_iff sem owner before after).mpr
        (unloadPath_lifecycle sem (by
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
