module

public import STC.State.Fiber
public import STC.State.FinmapAdapter

/-!
# Positive global state

`GlobalState` combines the finite fiber registry, dependent coeffect store,
lifetime freshness ledger, and immutable allocation history. Well-formedness is
an explicit conjunction of concrete structural predicates and semantic profile
obligations and never hides a support order.

## Main declarations

* `GlobalState`, `allocate`, `nextBirth`, `retire?`, `updateFiber`.
* `ProvidesNow` (active + committed table), `CommittedProvides` (teardown
  view), `providersOf` with well-formed-relative soundness/completeness/
  uniqueness.
* `targetProviders`, `targetSatisfied`, `targetView`, `TargetViewAt`,
  `TargetAbsent`, `Quiescent`, `stableImage` (D46 target/quiescence views).
* `Registered`, `Installed`, `Failed`, `PendingFlight` (D49).
* `WriteFrame`, `ReadNoninterference`, `ReadRespect`, `RegistrationFrame`,
  `CleanupFrame` (D48 confinement) plus pure state-update frame lemmas.
* `ReliedUpon` (D50).
* `ParentClosed`, `ParentAcyclic`, `TableConfined`, `ProvisionDisjoint`,
  `CommittedViewClosed`, `CommittedProvidersClosed`, `ActiveTableCoherent`,
  `CommittedViewDomain`, `IncarnationCoherent`, `AllocationCoherent`,
  `LedgerCoherent`, `WellFormedProfile`, `WellFormed` (D58).
* `FiberData`, `FiberCode`, `toPositiveRegistry`, `PositiveCellObs`,
  `toPositive_keys`, `toPositive_lookup_some`, `toPositive_lookup_none`,
  `toPositive_lookup_isSome_iff` (D32 representation of the concrete
  carrier; the T01C `PositiveContext` ambient pairing is universe-blocked,
  see the T02 handoff).
* `AlphaCodeProfile`, `NameNeutral`, `FactorizationProfile`, `ProgressProfile`,
  `ConfluenceProfile` (downstream theorem profiles).
-/

universe u v w x

namespace STC.State

open STC

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

local notation "GCell" =>
  FiberCell Name Key Value Action Iterator Accumulator Flight Failure

local notation "GComponent" => Component Key Value Action Iterator Accumulator Flight Failure

/-- The ordered allocation history is an immutable state component. -/
def issuedInOrder (state : GState) : List Name := state.allocationHistory

/-- Active names are derived by inspecting the positive registry cells;
retirement alone does not remove a name from the active set. -/
def activeNames (state : GState) : Finset Name :=
  state.registry.keys.filter fun name =>
    (Option.map (fun fiber : GCell => decide (fiber.phase = .active))
      (Finmap.lookup name state.registry)).getD false

/-- A derived active-store view; it does not replace the authoritative registry. -/
structure ActiveStoreView (Name : Type u) where
  active : Finset Name
  ordered : List Name

def activeStore (state : GState) : ActiveStoreView Name :=
  { active := activeNames state
    ordered := state.allocationHistory.filter fun n => n ∈ activeNames state }

/-- D46 stable-image projection: the active-set and allocation-order view used
by the derived Staging base macro. -/
def stableImage (state : GState) : ActiveStoreView Name := activeStore state

/-! ### Pure registry update and its frame laws -/

/-- A state update that changes only the selected registry cell. -/
def updateFiber (state : GState) (name : Name) (fiber : GCell) : GState :=
  { state with registry := Finmap.insert name fiber state.registry }

theorem updateFiber_coeffects (state : GState) (name : Name) (fiber : GCell) :
    (updateFiber state name fiber).coeffects = state.coeffects := rfl

theorem updateFiber_lookup_eq (state : GState) (name : Name) (fiber : GCell) :
    Finmap.lookup name (updateFiber state name fiber).registry = some fiber := by
  simp [updateFiber]

theorem updateFiber_lookup_ne (state : GState) {name other : Name} (h : other ≠ name)
    (fiber : GCell) :
    Finmap.lookup other (updateFiber state name fiber).registry =
      Finmap.lookup other state.registry := by
  simp [updateFiber, Finmap.lookup_insert_of_ne state.registry h]

theorem updateFiber_keys (state : GState) (name : Name) (fiber : GCell) :
    (updateFiber state name fiber).registry.keys = insert name state.registry.keys := by
  apply Finset.ext
  intro other
  simp [updateFiber]
  rw [Finmap.mem_keys]
  rw [Finmap.mem_insert]
  simp [Finmap.mem_keys]

theorem updateFiber_history (state : GState) (name : Name) (fiber : GCell) :
    (updateFiber state name fiber).allocationHistory = state.allocationHistory := rfl

theorem updateFiber_ledger (state : GState) (name : Name) (fiber : GCell) :
    (updateFiber state name fiber).ledger = state.ledger := rfl

/-! ### D47 allocation primitives -/

/-- D47 carrier primitive: allocate a fresh incarnation into the registry, the
ever-issued ledger, and the ordered allocation history. -/
def allocate (state : GState) (fresh : Name) (cell : GCell) : GState :=
  { state with
      registry := Finmap.insert fresh cell state.registry
      ledger := { everIssued := insert fresh state.ledger.everIssued }
      allocationHistory := state.allocationHistory ++ [fresh] }

/-- The birth index of the next allocation. -/
def nextBirth (state : GState) : Nat := state.allocationHistory.length

theorem allocate_lookup_fresh (state : GState) (fresh : Name) (cell : GCell) :
    Finmap.lookup fresh (allocate state fresh cell).registry = some cell := by
  simp [allocate]

theorem allocate_lookup_ne (state : GState) (fresh : Name) (cell : GCell)
    {name : Name} (h : name ≠ fresh) :
    Finmap.lookup name (allocate state fresh cell).registry =
      Finmap.lookup name state.registry := by
  simp [allocate, Finmap.lookup_insert_of_ne state.registry h]

theorem allocate_keys (state : GState) (fresh : Name) (cell : GCell) :
    (allocate state fresh cell).registry.keys = insert fresh state.registry.keys := by
  apply Finset.ext
  intro name
  simp [allocate]
  rw [Finmap.mem_keys]
  rw [Finmap.mem_insert]
  simp [Finmap.mem_keys]

theorem allocate_history (state : GState) (fresh : Name) (cell : GCell) :
    (allocate state fresh cell).allocationHistory = state.allocationHistory ++ [fresh] := rfl

theorem allocate_ledger (state : GState) (fresh : Name) (cell : GCell) :
    (allocate state fresh cell).ledger.everIssued = insert fresh state.ledger.everIssued := rfl

theorem allocate_coeffects (state : GState) (fresh : Name) (cell : GCell) :
    (allocate state fresh cell).coeffects = state.coeffects := rfl

theorem allocate_ambient (state : GState) (fresh : Name) (cell : GCell) :
    (allocate state fresh cell).ambient = state.ambient := rfl

/-- D47 retirement inverse: flip the retired flag of the selected cell. -/
def retire? (state : GState) (name : Name) : Option GState :=
  (Finmap.lookup name state.registry).map fun cell =>
    updateFiber state name { cell with retired := true }

theorem retire?_none_iff (state : GState) (name : Name) :
    retire? state name = none ↔ Finmap.lookup name state.registry = none := by
  cases h : Finmap.lookup name state.registry <;> simp [retire?, h]

theorem retire?_some_iff (state : GState) (name : Name) {cell : GCell}
    (h : Finmap.lookup name state.registry = some cell) :
    retire? state name = some (updateFiber state name { cell with retired := true }) := by
  simp [retire?, h]

theorem retire?_retired {state : GState} {name : Name} {after : GState} {cell : GCell}
    (h : retire? state name = some after)
    (hlook : Finmap.lookup name after.registry = some cell) :
    cell.retired = true := by
  cases hlook0 : Finmap.lookup name state.registry with
  | none => simp [retire?, hlook0] at h
  | some cell0 =>
      have hafter : after = updateFiber state name { cell0 with retired := true } := by
        simp [retire?, hlook0] at h
        exact h.symm
      subst after
      rw [updateFiber_lookup_eq] at hlook
      have hcell : cell = { cell0 with retired := true } := (Option.some.inj hlook).symm
      rw [hcell]

/-! ### D48 write-frame and read-noninterference -/

/-- D48 write-frame: a successor may differ from the source only in the owner's
cell and in coeffect keys the owner declares it provides; the name ledger and
the allocation history are fixed. -/
def WriteFrame (state : GState) (owner : Name) (after : GState) : Prop :=
  (∀ name, name ≠ owner →
      Finmap.lookup name state.registry = Finmap.lookup name after.registry) ∧
    (match Finmap.lookup owner state.registry with
     | some cell => ∀ key, key ∉ cell.component.provides →
         Coeffect.lookup key state.coeffects = Coeffect.lookup key after.coeffects
     | none => True) ∧
      state.ledger = after.ledger ∧ state.allocationHistory = after.allocationHistory

/-- D48 read-noninterference: the owner's required keys observe the same values
across the step. -/
def ReadNoninterference (state : GState) (owner : Name) (after : GState) : Prop :=
  match Finmap.lookup owner state.registry with
  | some cell => ∀ key, key ∈ cell.component.requires →
      Coeffect.lookup key state.coeffects = Coeffect.lookup key after.coeffects
  | none => True

/-- A cell update satisfies the D48 write-frame relative to the owner. -/
theorem updateFiber_writeFrame (state : GState) (owner : Name) (fiber : GCell) :
    WriteFrame state owner (updateFiber state owner fiber) := by
  unfold WriteFrame
  constructor
  · intro name hne
    exact (updateFiber_lookup_ne state hne fiber).symm
  · constructor
    · cases Finmap.lookup owner state.registry with
      | some _ => intro key _; simp [updateFiber]
      | none => trivial
    · simp [updateFiber]

/-- A cell update satisfies the D48 read-noninterference condition. -/
theorem updateFiber_readNoninterference (state : GState) (owner : Name) (fiber : GCell) :
    ReadNoninterference state owner (updateFiber state owner fiber) := by
  unfold ReadNoninterference
  cases Finmap.lookup owner state.registry with
  | some _ => intro key _; simp [updateFiber]
  | none => trivial

/-- D48 two-run read-respect: across two executions, the owner's required keys
read the same values. -/
def ReadRespect (left right : GState) (owner : Name) : Prop :=
  ∀ cell key, Finmap.lookup owner left.registry = some cell →
    key ∈ cell.component.requires →
      Coeffect.lookup key left.coeffects = Coeffect.lookup key right.coeffects

/-- A cell update satisfies the two-run read-respect condition. -/
theorem updateFiber_readRespect (state : GState) (owner : Name) (fiber : GCell) :
    ReadRespect state (updateFiber state owner fiber) owner := by
  unfold ReadRespect
  intro cell key _hlook _hkey
  simp [updateFiber]

/-- D48 registration frame: the registry grows only at `fresh` by `cell`, the
ever-issued ledger only at `fresh`, the allocation history only appends `fresh`,
and the ambient/coeffect stores and all other cells are fixed. -/
def RegistrationFrame (state : GState) (fresh : Name) (cell : GCell) (after : GState) : Prop :=
  (∀ name, name ≠ fresh →
      Finmap.lookup name state.registry = Finmap.lookup name after.registry) ∧
    Finmap.lookup fresh state.registry = none ∧
      Finmap.lookup fresh after.registry = some cell ∧
        fresh ∉ state.ledger.everIssued ∧
          after.ledger.everIssued = insert fresh state.ledger.everIssued ∧
            after.allocationHistory = state.allocationHistory ++ [fresh] ∧
              after.coeffects = state.coeffects ∧ after.ambient = state.ambient

/-- The D47 allocation primitive satisfies the registration frame. -/
theorem allocate_registrationFrame (state : GState) {fresh : Name} {cell : GCell}
    (hfresh : Finmap.lookup fresh state.registry = none)
    (hledger : fresh ∉ state.ledger.everIssued) :
    RegistrationFrame state fresh cell (allocate state fresh cell) := by
  unfold RegistrationFrame
  constructor
  · intro name hne
    exact (allocate_lookup_ne state fresh cell hne).symm
  · constructor
    · exact hfresh
    · constructor
      · exact allocate_lookup_fresh state fresh cell
      · constructor
        · exact hledger
        · constructor
          · exact allocate_ledger state fresh cell
          · constructor
            · exact allocate_history state fresh cell
            · constructor
              · exact allocate_coeffects state fresh cell
              · exact allocate_ambient state fresh cell

/-- D48 teardown frame: accumulator execution during unload may edit the owner's
cell and apply recorded child-retirement inverses (flipping a child's retired
flag), nothing else; the ledger, history, and coeffect store are fixed. -/
def CleanupFrame (state : GState) (owner : Name) (after : GState) : Prop :=
  (∀ name, name ≠ owner →
      Finmap.lookup name state.registry = Finmap.lookup name after.registry ∨
        ∃ cell, Finmap.lookup name state.registry = some cell ∧ cell.retired = false ∧
          Finmap.lookup name after.registry = some { cell with retired := true }) ∧
    state.ledger = after.ledger ∧ state.allocationHistory = after.allocationHistory ∧
      state.coeffects = after.coeffects

/-- A pure owner-cell update satisfies the teardown frame. -/
theorem updateFiber_cleanupFrame (state : GState) (owner : Name) (fiber : GCell) :
    CleanupFrame state owner (updateFiber state owner fiber) := by
  unfold CleanupFrame
  constructor
  · intro name hne
    left
    exact (updateFiber_lookup_ne state hne fiber).symm
  · simp [updateFiber]

/-- Flipping a child's retired flag satisfies the teardown frame of any owner. -/
theorem retire?_cleanupFrame {state : GState} {owner child : Name} {cell : GCell}
    (hlook : Finmap.lookup child state.registry = some cell)
    (hret : cell.retired = false) :
    CleanupFrame state owner (updateFiber state child { cell with retired := true }) := by
  unfold CleanupFrame
  constructor
  · intro name hne'
    by_cases hname : name = child
    · right
      refine ⟨cell, ?_, hret, ?_⟩
      · rw [hname]
        exact hlook
      · rw [hname]
        exact updateFiber_lookup_eq state child { cell with retired := true }
    · left
      exact (updateFiber_lookup_ne state (by intro h; exact hname h)
        { cell with retired := true }).symm
  · simp [updateFiber]

/-! ### D45 provider relation and executable selection -/

/-- D45 provider relation: the provider is active and its committed local table
actually contains the key. Retirement alone does not stop a binding; only
leaving the active phase or erasure does. -/
def ProvidesNow (state : GState) (provider : Name) (key : Key) : Prop :=
  ∃ fiber, Finmap.lookup provider state.registry = some fiber ∧
    key ∈ fiber.committed.entries.keys ∧ fiber.phase = .active

/-- D45 teardown provider relation: active or unloading providers whose
committed table contains the key; used by old committed views during teardown. -/
def CommittedProvides (state : GState) (provider : Name) (key : Key) : Prop :=
  ∃ fiber, Finmap.lookup provider state.registry = some fiber ∧
    key ∈ fiber.committed.entries.keys ∧ (fiber.phase = .active ∨ fiber.phase = .unloading)

/-- The executable provider set for one requirement key: active registry cells
whose committed table contains the key. -/
abbrev providersOf (state : GState) (key : Key) : Finset Name :=
  state.registry.keys.filter fun name =>
    (Option.map (fun fiber : GCell =>
        decide (key ∈ fiber.committed.entries.keys ∧ fiber.phase = .active))
      (Finmap.lookup name state.registry)).getD false

theorem providersOf_sound (state : GState) {key : Key} {provider : Name}
    (h : provider ∈ providersOf state key) : ProvidesNow state provider key := by
  rw [Finset.mem_filter] at h
  rcases h with ⟨_hkeys, hprov⟩
  rcases hlook : Finmap.lookup provider state.registry with _ | fiber
  · simp [hlook] at hprov
  · have hdec : key ∈ fiber.committed.entries.keys ∧ fiber.phase = .active :=
      of_decide_eq_true (by simpa [hlook] using hprov)
    exact ⟨fiber, hlook, hdec.1, hdec.2⟩

theorem providersOf_complete (state : GState) {key : Key} {provider : Name}
    (h : ProvidesNow state provider key) : provider ∈ providersOf state key := by
  rcases h with ⟨fiber, hlook, hkey, hphase⟩
  rw [Finset.mem_filter]
  constructor
  · rw [Finmap.mem_keys, ← Finmap.lookup_isSome, hlook]
    simp
  · simp [hlook, hkey, hphase]

/-! ### D46 target view and quiescence -/

/-- D46 target view data: the providers currently resolving `name`'s
requirements. -/
abbrev targetProviders (state : GState) (name : Name) : Finset Name :=
  (Option.map (fun cell : GCell =>
      state.registry.keys.filter fun provider =>
        cell.component.requires.filter (fun key => provider ∈ providersOf state key) ≠ ∅)
    (Finmap.lookup name state.registry)).getD ∅

/-- D46: every required key has a current provider. -/
abbrev targetSatisfied (state : GState) (name : Name) : Prop :=
  (Option.map (fun cell : GCell =>
      decide (cell.component.requires.filter (fun key => (providersOf state key) = ∅) = ∅))
    (Finmap.lookup name state.registry)).getD false

/-- D46: the target view is the provider set exactly when all requirements are
satisfied, and `none` marks an unsatisfied dependency. -/
abbrev targetView (state : GState) (name : Name) : Option (Finset Name) :=
  if _ : targetSatisfied state name then some (targetProviders state name) else none

theorem targetSatisfied_iff (state : GState) (name : Name) {cell : GCell}
    (hlook : Finmap.lookup name state.registry = some cell) :
    targetSatisfied state name ↔
      ∀ key, key ∈ cell.component.requires → (providersOf state key).Nonempty := by
  unfold targetSatisfied
  rw [hlook]
  simp [Finset.nonempty_iff_ne_empty]

theorem targetView_isSome_iff (state : GState) (name : Name) :
    (targetView state name).isSome ↔ targetSatisfied state name := by
  by_cases h : targetSatisfied state name <;> simp [h]

theorem targetView_some_iff (state : GState) (name : Name) (providers : Finset Name) :
    targetView state name = some providers ↔
      targetSatisfied state name ∧ providers = targetProviders state name := by
  by_cases h : targetSatisfied state name <;> grind only

theorem targetView_mem (state : GState) (name : Name) {cell : GCell} {providers : Finset Name}
    (h : targetView state name = some providers)
    (hlook : Finmap.lookup name state.registry = some cell) {provider : Name} :
    provider ∈ providers ↔
      ∃ key, key ∈ cell.component.requires ∧ provider ∈ providersOf state key := by
  have hs := (targetView_some_iff state name providers).mp h
  rw [hs.2]
  unfold targetProviders
  rw [hlook]
  change provider ∈ (state.registry.keys.filter fun p =>
      cell.component.requires.filter (fun key => p ∈ providersOf state key) ≠ ∅) ↔
    ∃ key, key ∈ cell.component.requires ∧ provider ∈ providersOf state key
  rw [Finset.mem_filter]
  constructor
  · intro ⟨_hkeys, hnonempty⟩
    rw [← Finset.nonempty_iff_ne_empty] at hnonempty
    rcases hnonempty with ⟨key, hk⟩
    rw [Finset.mem_filter] at hk
    exact ⟨key, hk.1, hk.2⟩
  · intro ⟨key, hk, hp⟩
    constructor
    · rw [Finmap.mem_keys]
      rcases providersOf_sound state hp with ⟨fiber, hf, _htable, _hphase⟩
      rw [← Finmap.lookup_isSome, hf]
      simp
    · rw [← Finset.nonempty_iff_ne_empty]
      exact ⟨key, by rw [Finset.mem_filter]; exact ⟨hk, hp⟩⟩

/-- A provider in the target view provides some required key. -/
theorem targetView_provides (state : GState) (name : Name) {cell : GCell}
    {providers : Finset Name} (h : targetView state name = some providers)
    (hlook : Finmap.lookup name state.registry = some cell)
    {key : Key} {provider : Name} (hkey : key ∈ cell.component.requires)
    (hprov : provider ∈ providersOf state key) :
    provider ∈ providers ∧ ProvidesNow state provider key := by
  exact ⟨(targetView_mem state name h hlook).mpr ⟨key, hkey, hprov⟩,
    providersOf_sound state hprov⟩

/-! ### D46 target view at a given committed view -/

/-- D46: `ω` is the exact current target view of `owner`: the owner itself is a
currently eligible, non-retired fiber, its domain is exactly the owner's
required keys, and every entry names a current provider of that key.  A
retired Active provider may still satisfy a dependent's committed binding
(`ProvidesNow` does not check retirement), but the retired fiber itself has
no current target. -/
def TargetViewAt (state : GState) (owner : Name)
    (ω : Finmap (fun _ : Key => Name)) : Prop :=
  ∃ cell, Finmap.lookup owner state.registry = some cell ∧ cell.retired = false ∧
    ω.keys = cell.component.requires ∧
      ∀ key provider, Finmap.lookup key ω = some provider → ProvidesNow state provider key

/-- D46: no view is a target — some required key has no current provider. -/
def TargetAbsent (state : GState) (owner : Name) : Prop :=
  ∀ ω, ¬ TargetViewAt state owner ω

/-! ### D49 installed/failed views and quiescence -/

/-- The name has a current registry cell, regardless of phase. -/
def Registered (state : GState) (name : Name) : Prop :=
  ∃ fiber, Finmap.lookup name state.registry = some fiber

/-- D49 installed predicate: the name's cell is mid-lifecycle or active. -/
def Installed (state : GState) (name : Name) : Prop :=
  ∃ fiber, Finmap.lookup name state.registry = some fiber ∧
    (fiber.phase = .reloading ∨ fiber.phase = .active ∨ fiber.phase = .unloading)

/-- Installed names are registered. -/
theorem installed_registered (state : GState) {name : Name}
    (h : Installed state name) : Registered state name := by
  rcases h with ⟨fiber, hlook, _hphase⟩
  exact ⟨fiber, hlook⟩

/-- D49 failed predicate: the name's cell is in the failed phase. -/
def Failed (state : GState) (name : Name) : Prop :=
  ∃ cell, Finmap.lookup name state.registry = some cell ∧ cell.phase = .failed

/-- D49: the name's cell carries an in-flight payload. -/
def PendingFlight (state : GState) (name : Name) : Prop :=
  ∃ cell, Finmap.lookup name state.registry = some cell ∧ cell.payload.flightCode.isSome

/-- Extended quiescence reflects lifecycle/target agreement: no fiber is
mid-transition, no flight is pending, every active fiber's committed view is
its exact current target, and a normal non-retired inactive fiber has no
available target (L-Begin would be enabled).  A retired inactive fiber may be
terminal and a failed fiber is terminal under the failure policy. -/
def Quiescent (state : GState) : Prop :=
  ∀ name fiber, Finmap.lookup name state.registry = some fiber →
    fiber.phase ≠ .reloading ∧ fiber.phase ≠ .unloading ∧ fiber.payload.flightCode = none ∧
      (fiber.phase = .active → TargetViewAt state name fiber.committedView) ∧
        (fiber.phase = .inactive → fiber.retired = true ∨ TargetAbsent state name)

/-! ### D50 relied-upon relation -/

/-- D50 relied-upon: a distinct installed dependent is bound through its
committed provider view to `provider` for some declared requirement key. -/
def ReliedUpon (state : GState) (dependent provider : Name) : Prop :=
  dependent ≠ provider ∧ Installed state dependent ∧
    ∃ cell key, Finmap.lookup dependent state.registry = some cell ∧
      key ∈ cell.component.requires ∧
        Finmap.lookup key cell.committedView = some provider

theorem reliedUpon_iff_view (state : GState) {cell : GCell} {dependent provider : Name}
    (hlook : Finmap.lookup dependent state.registry = some cell)
    (hinst : Installed state dependent) (hne : dependent ≠ provider) :
    ReliedUpon state dependent provider ↔
      ∃ key, key ∈ cell.component.requires ∧
        Finmap.lookup key cell.committedView = some provider := by
  constructor
  · rintro ⟨_hne, _hinst, c, key, hc, hkey, hk⟩
    rw [hlook] at hc
    rcases hc
    exact ⟨key, hkey, hk⟩
  · intro h
    rcases h with ⟨key, hkey, hk⟩
    exact ⟨hne, hinst, cell, key, hlook, hkey, hk⟩

/-! ### D58 well-formed registry -/

/-- The parent step of a registry: `child`'s parent field names `parent`. -/
def ParentStep (state : GState) (parent child : Name) : Prop :=
  ∃ cell, Finmap.lookup child state.registry = some cell ∧ cell.parent = some parent

/-- Every parent reference names an installed fiber. -/
def ParentClosed (state : GState) : Prop :=
  ∀ name cell, Finmap.lookup name state.registry = some cell →
    match cell.parent with
    | some parent => parent ∈ state.registry.keys
    | none => True

/-- The parent graph of the registry is acyclic. -/
def ParentAcyclic (state : GState) : Prop :=
  WellFounded (ParentStep state)

/-- Each fiber's local committed table is confined to its declared provisions. -/
def TableConfined (state : GState) : Prop :=
  ∀ name cell, Finmap.lookup name state.registry = some cell →
    cell.committed.entries.keys ⊆ cell.component.provides

/-- Distinct installed components declare disjoint provision sets. -/
def ProvisionDisjoint (state : GState) : Prop :=
  ∀ {a b} {ca cb}, Finmap.lookup a state.registry = some ca →
    Finmap.lookup b state.registry = some cb → a ≠ b →
    Disjoint ca.component.provides cb.component.provides

/-- Every committed provider-view entry names an installed fiber. -/
def CommittedViewClosed (state : GState) : Prop :=
  ∀ name cell, Finmap.lookup name state.registry = some cell →
    ∀ key provider, Finmap.lookup key cell.committedView = some provider →
      provider ∈ state.registry.keys

/-- Committed provider-view entries name fibers that currently provide the key,
including unloading teardown providers. -/
def CommittedProvidersClosed (state : GState) : Prop :=
  ∀ name cell, Finmap.lookup name state.registry = some cell →
    ∀ key provider, Finmap.lookup key cell.committedView = some provider →
      CommittedProvides state provider key

/-- Active fibers' committed tables are folded into the ambient coeffect store
domain. -/
def ActiveTableCoherent (state : GState) : Prop :=
  ∀ name cell, Finmap.lookup name state.registry = some cell → cell.phase = .active →
    cell.committed.entries.keys ⊆ state.coeffects.keys

/-- Every committed provider-view entry lies in the fiber's declared
requirements. -/
def CommittedViewDomain (state : GState) : Prop :=
  ∀ name cell, Finmap.lookup name state.registry = some cell →
    cell.committedView.keys ⊆ cell.component.requires

/-- A cell's incarnation field agrees with its registry key. -/
def IncarnationCoherent (state : GState) : Prop :=
  ∀ name cell, Finmap.lookup name state.registry = some cell → cell.incarnation = name

/-- The allocation history is duplicate-free and every cell's birth index points
at its own name. -/
def AllocationCoherent (state : GState) : Prop :=
  state.allocationHistory.Nodup ∧
    ∀ name cell, Finmap.lookup name state.registry = some cell →
      cell.birth < state.allocationHistory.length ∧
        state.allocationHistory[cell.birth]? = some name

/-- Registry and history names are all ever-issued. -/
def LedgerCoherent (state : GState) : Prop :=
  state.registry.keys ⊆ state.ledger.everIssued ∧
    ∀ name, name ∈ state.allocationHistory → name ∈ state.ledger.everIssued

/-- The five data-coherence invariants bundled for `WellFormed`. -/
def DataCoherent (state : GState) : Prop :=
  ActiveTableCoherent state ∧ CommittedViewDomain state ∧ IncarnationCoherent state ∧
    AllocationCoherent state ∧ LedgerCoherent state

/-- The three state-local obligations that depend on the ambient lifecycle
semantics; every structural invariant is a concrete predicate above. -/
structure WellFormedProfile
    (Name : Type u) (Key : Type v) (Value : Type w)
    (Action : Type u) (Iterator : Type v) (Accumulator : Type w)
    (Flight : Type u) (Failure : Type v) (Ambient : Type x)
    [DecidableEq Name] [DecidableEq Key] where
  lifecycleCoherent :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  root : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  declarations :
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop

local notation "WFProfile" =>
  WellFormedProfile Name Key Value Action Iterator Accumulator Flight Failure Ambient

/-- D58 well-formed registry: the six structural invariants, the five
data-coherence invariants, and the three semantic profile obligations, each
visibly separate. -/
def WellFormed (profile : WFProfile) (state : GState) : Prop :=
  ParentClosed state ∧ ParentAcyclic state ∧ TableConfined state ∧ ProvisionDisjoint state ∧
    CommittedViewClosed state ∧ CommittedProvidersClosed state ∧ DataCoherent state ∧
      profile.lifecycleCoherent state ∧ profile.root state ∧ profile.declarations state

theorem wellFormed_parentClosed (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : ParentClosed state := h.1

theorem wellFormed_parentAcyclic (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : ParentAcyclic state := h.2.1

theorem wellFormed_tableConfined (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : TableConfined state := h.2.2.1

theorem wellFormed_provisionDisjoint (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : ProvisionDisjoint state := h.2.2.2.1

theorem wellFormed_committedViewClosed (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : CommittedViewClosed state := h.2.2.2.2.1

theorem wellFormed_committedProvidersClosed (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : CommittedProvidersClosed state := h.2.2.2.2.2.1

theorem wellFormed_dataCoherent (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : DataCoherent state := h.2.2.2.2.2.2.1

theorem wellFormed_lifecycleCoherent (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : profile.lifecycleCoherent state := h.2.2.2.2.2.2.2.1

theorem wellFormed_root (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : profile.root state := h.2.2.2.2.2.2.2.2.1

theorem wellFormed_declarations (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : profile.declarations state := h.2.2.2.2.2.2.2.2.2

theorem wellFormed_activeTableCoherent (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : ActiveTableCoherent state :=
  (wellFormed_dataCoherent profile h).1

theorem wellFormed_committedViewDomain (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : CommittedViewDomain state :=
  (wellFormed_dataCoherent profile h).2.1

theorem wellFormed_incarnationCoherent (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : IncarnationCoherent state :=
  (wellFormed_dataCoherent profile h).2.2.1

theorem wellFormed_allocationCoherent (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : AllocationCoherent state :=
  (wellFormed_dataCoherent profile h).2.2.2.1

theorem wellFormed_ledgerCoherent (profile : WFProfile) {state : GState}
    (h : WellFormed profile state) : LedgerCoherent state :=
  (wellFormed_dataCoherent profile h).2.2.2.2

/-! ### Well-formed-relative provider uniqueness -/

theorem providersOf_unique (profile : WFProfile)
    {state : GState} {key : Key} {left right : Name} (hWF : WellFormed profile state)
    (hleft : left ∈ providersOf state key) (hright : right ∈ providersOf state key) :
    left = right := by
  by_contra hne
  rcases providersOf_sound state hleft with ⟨lf, hl, hkl, _hlp⟩
  rcases providersOf_sound state hright with ⟨rf, hr, hkr, _hrp⟩
  have hklp : key ∈ lf.component.provides :=
    (wellFormed_tableConfined profile hWF) left lf hl hkl
  have hkrp : key ∈ rf.component.provides :=
    (wellFormed_tableConfined profile hWF) right rf hr hkr
  have hdisj : Disjoint lf.component.provides rf.component.provides :=
    (wellFormed_provisionDisjoint profile hWF) hl hr hne
  exact (Finset.disjoint_left.mp hdisj hklp) hkrp

theorem providersOf_card_le_one (profile : WFProfile)
    {state : GState} {key : Key} (hWF : WellFormed profile state) :
    (providersOf state key).card ≤ 1 := by
  by_cases h : (providersOf state key).Nonempty
  · rcases h with ⟨p, hp⟩
    have hsingleton : providersOf state key = {p} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hp, by intro y hy; exact providersOf_unique profile hWF hy hp⟩
    rw [hsingleton]
    simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

/-! ### D32 positive representation -/

/-- The name/data/code split of a fiber cell: name-bearing data lives in
`FiberData`, all executable codes in `FiberCode`. -/
structure FiberData (Name : Type u) (Key : Type v) (Value : Type w) where
  parent : Option Name
  birth : Nat
  requires : Finset Key
  provides : Finset Key
  committed : CommittedData Key Value
  committedView : Finmap (fun _ : Key => Name)
  retired : Bool
  phase : LifecyclePhase

structure FiberCode (Action : Type u) (Iterator : Type v) (Accumulator : Type w)
    (Flight : Type u) (Failure : Type v) where
  actionCode : Action
  iteratorCode : Iterator
  accumulatorCode : Accumulator
  flightCode : Option Flight
  failureData : Option Failure

def fiberData (cell : GCell) : FiberData Name Key Value :=
  { parent := cell.parent, birth := cell.birth, requires := cell.component.requires,
    provides := cell.component.provides, committed := cell.committed,
    committedView := cell.committedView, retired := cell.retired, phase := cell.phase }

def fiberCode (cell : GCell) : FiberCode Action Iterator Accumulator Flight Failure :=
  { actionCode := cell.component.actionCode, iteratorCode := cell.component.iteratorCode,
    accumulatorCode := cell.component.accumulatorCode,
    flightCode := cell.payload.flightCode, failureData := cell.payload.failureData }

def toPositiveCell (cell : GCell) :
    PositiveCell Name (FiberData Name Key Value)
      (FiberCode Action Iterator Accumulator Flight Failure) :=
  { key := cell.incarnation, data := fiberData cell, code := fiberCode cell }

/-- The concrete registry re-presented as positive cell entries. -/
def toPositiveEntries (state : GState) :
    Multiset (Sigma (fun _ : Name => PositiveCell Name (FiberData Name Key Value)
      (FiberCode Action Iterator Accumulator Flight Failure))) :=
  state.registry.entries.map fun entry => ⟨entry.1, toPositiveCell entry.2⟩

theorem toPositiveEntries_keys (state : GState) :
    Multiset.keys (toPositiveEntries state) = Multiset.keys state.registry.entries := by
  unfold toPositiveEntries
  unfold Multiset.keys
  rw [Multiset.map_map]
  congr 1

theorem toPositiveEntries_nodupKeys (state : GState) : (toPositiveEntries state).NodupKeys := by
  rw [← Multiset.nodup_keys]
  rw [toPositiveEntries_keys]
  rw [Multiset.nodup_keys]
  exact state.registry.nodupKeys

/-- D32: the concrete registry as a positive data/code registry. -/
def toPositiveRegistry (state : GState) :
    PositiveRegistry Name (FiberData Name Key Value)
      (FiberCode Action Iterator Accumulator Flight Failure) :=
  ⟨toPositiveEntries state, toPositiveEntries_nodupKeys state⟩

theorem toPositiveRegistry_entries (state : GState) :
    (toPositiveRegistry state).entries = toPositiveEntries state := rfl

/-- The cellwise correspondence between the positive representation and the
concrete fiber cell. -/
def PositiveCellObs (cell : PositiveCell Name (FiberData Name Key Value)
    (FiberCode Action Iterator Accumulator Flight Failure)) (fiber : GCell) : Prop :=
  cell.key = fiber.incarnation ∧ cell.data = fiberData fiber ∧ cell.code = fiberCode fiber

theorem toPositive_keys (state : GState) :
    (toPositiveRegistry state).keys = state.registry.keys := by
  apply Finset.ext
  intro name
  rw [Finmap.mem_keys, Finmap.mem_keys]
  rw [Finmap.mem_def, Finmap.mem_def]
  rw [toPositiveRegistry_entries]
  rw [toPositiveEntries_keys]

/-- The D32 representation theorem, some-direction: a concrete cell is
re-presented by its positive data/code cell. -/
theorem toPositive_lookup_some (state : GState) (name : Name) {fiber : GCell}
    (h : Finmap.lookup name state.registry = some fiber) :
    Finmap.lookup name (toPositiveRegistry state) = some (toPositiveCell fiber) := by
  rw [Finmap.lookup_eq_some_iff]
  rw [toPositiveRegistry_entries]
  exact Multiset.mem_map.mpr ⟨Sigma.mk name fiber,
    (Finmap.lookup_eq_some_iff (s := state.registry) (a := name) (b := fiber)).mp h, rfl⟩

/-- The D32 representation theorem, none-direction: absent cells stay absent. -/
theorem toPositive_lookup_none (state : GState) (name : Name)
    (h : Finmap.lookup name state.registry = none) :
    Finmap.lookup name (toPositiveRegistry state) = none := by
  by_contra hneq
  have ⟨cell, hcell⟩ := Option.ne_none_iff_exists.mp hneq
  have hcell' : Finmap.lookup name (toPositiveRegistry state) = some cell := hcell.symm
  rw [Finmap.lookup_eq_some_iff] at hcell'
  rw [toPositiveRegistry_entries] at hcell'
  rw [toPositiveEntries] at hcell'
  rw [Multiset.mem_map] at hcell'
  rcases hcell' with ⟨entry, hentry, hcellEq⟩
  have hkey : entry.1 = name := congrArg Sigma.fst hcellEq
  change Sigma.mk entry.1 entry.2 ∈ state.registry.entries at hentry
  rw [hkey] at hentry
  have hlook : Finmap.lookup name state.registry = some entry.2 :=
    (Finmap.lookup_eq_some_iff (s := state.registry) (a := name) (b := entry.2)).mpr hentry
  rw [h] at hlook
  cases hlook

/-- The D32 representation theorem: definedness is preserved key by key. -/
theorem toPositive_lookup_isSome_iff (state : GState) (name : Name) :
    (Finmap.lookup name (toPositiveRegistry state)).isSome ↔
      (Finmap.lookup name state.registry).isSome := by
  constructor
  · intro h
    cases hlook : Finmap.lookup name (toPositiveRegistry state) with
    | none => simp [hlook] at h
    | some cell =>
        have hmem : Sigma.mk name cell ∈ (toPositiveRegistry state).entries :=
          (Finmap.lookup_eq_some_iff (s := toPositiveRegistry state) (a := name)
            (b := cell)).mp hlook
        rw [toPositiveRegistry_entries] at hmem
        rw [toPositiveEntries] at hmem
        rw [Multiset.mem_map] at hmem
        rcases hmem with ⟨entry, hentry, hcellEq⟩
        have hkey : entry.1 = name := congrArg Sigma.fst hcellEq
        change Sigma.mk entry.1 entry.2 ∈ state.registry.entries at hentry
        rw [hkey] at hentry
        have hname : name ∈ state.registry :=
          Finmap.mem_def.mpr (Multiset.mem_map_of_mem Sigma.fst hentry)
        exact (Finmap.lookup_isSome (s := state.registry) (a := name)).mpr hname
  · intro h
    cases hlook : Finmap.lookup name state.registry with
    | none => simp [hlook] at h
    | some fiber => simp [toPositive_lookup_some state name hlook]

/-! ### Downstream theorem profiles -/

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

/-- A code family is name-neutral exactly when every renaming acts as the
identity. -/
def NameNeutral {Code : Type u} {State : Type v}
    (profile : AlphaCodeProfile Name Code State) : Prop :=
  ∀ χ code, profile.act χ code = code

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
