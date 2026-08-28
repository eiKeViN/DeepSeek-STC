module

public import STC.State.CoeffectStore
public import STC.State.FinmapAdapter
public import STC.State.Observation
public import STC.State.Toy

/-!
# Finite state, registry, and coeffect evidence

This module evaluates the P5 interfaces on finite positive and negative
fixtures. The uniform `ToyRegistry` and dependent ADR-02 coeffect store remain
separate, while the observation examples distinguish lifecycle, control-erased,
and name-aware views.

## Main declarations

* `StateReport`: the finite executable result record.
* `stateReport_expected`: the kernel-checked expected-output theorem.
-/

namespace STC

@[expose] public section

abbrev toyApi : RegistryLike ToyKey ToyValue (ToyRegistry ToyKey ToyValue) :=
  toyRegistryLike

def insertedToy : ToyRegistry ToyKey ToyValue :=
  toyApi.insert toyApi.empty .alpha .first

def overwrittenToy : ToyRegistry ToyKey ToyValue :=
  toyApi.insert toyExample .alpha .second

def erasedToy : Option (ToyValue × ToyRegistry ToyKey ToyValue) :=
  erasePresent? toyApi toyExample .beta

def freshThenErase : ToyRegistry ToyKey ToyValue :=
  toyApi.erase (toyApi.insert toyApi.empty .alpha .first) .alpha

def capturedEraseThenInsert : ToyRegistry ToyKey ToyValue :=
  toyApi.insert (toyApi.erase toyExample .beta) .beta .second

/-- Compare every key of the finite Toy fixture without assuming carrier equality. -/
def sameToyLookups (left right : ToyRegistry ToyKey ToyValue) : Bool :=
  decide (
    toyApi.lookup left .alpha = toyApi.lookup right .alpha ∧
      toyApi.lookup left .beta = toyApi.lookup right .beta ∧
        toyApi.lookup left .gamma = toyApi.lookup right .gamma)

/-- A raw candidate insertion that violates the Toy key-uniqueness invariant. -/
def duplicateCandidate : List (ToyKey × ToyValue) :=
  (.alpha, .second) :: toyExample.entries

/-! ## Dependent ADR-02 store fixture -/

/-- Two coeffect keys whose associated value types differ. -/
inductive DepKey : Type
  | natKey
  | boolKey
  deriving DecidableEq, Repr

/-- A genuinely dependent family: one key stores `Nat`, the other stores `Bool`. -/
abbrev DepValue : DepKey → Type
  | .natKey => Nat
  | .boolKey => Bool

/-- A finite dependent coeffect store, distinct from the uniform Toy registry. -/
def depStore : Coeffect.Store DepValue :=
  Coeffect.insert .natKey 7
    (Coeffect.insert .boolKey true (∅ : Coeffect.Store DepValue))

/-! ## Distinct observation profiles -/

/-- A finite carrier with core, lifecycle, control, and name components. -/
structure ProfileState where
  core : Nat
  life : Bool
  control : Bool
  name : ToyKey
  deriving DecidableEq, Repr

def profileStateLike : StateLike ProfileState Nat :=
  ⟨fun state ↦ state.core⟩

def profileCore : RelSpec ProfileState :=
  CoreStateObs profileStateLike (equality Nat)

def lifeProfile : ObservationProfile ProfileState Bool :=
  ObservationProfile.exactEquality fun state ↦ state.life

def controlProfile : ObservationProfile ProfileState Bool :=
  ObservationProfile.exactEquality fun state ↦ state.control

def nameProfile : ObservationProfile ProfileState ToyKey :=
  ObservationProfile.exactEquality fun state ↦ state.name

def erasedProfile : ObservationProfile ProfileState (Nat × ToyKey) :=
  ObservationProfile.exactEquality fun state ↦ (state.core, state.name)

def lifecycleProfile : RelSpec ProfileState :=
  LifecycleObs profileCore lifeProfile controlProfile

def eraseControlProfile : RelSpec ProfileState :=
  EraseControl erasedProfile

def nameAwareProfile : RelSpec ProfileState :=
  NameAwareObs profileCore nameProfile

def lifecycleLeft : ProfileState :=
  { core := 1, life := true, control := false, name := .alpha }

def lifecycleRight : ProfileState :=
  { core := 1, life := true, control := false, name := .beta }

def eraseControlLeft : ProfileState :=
  { core := 2, life := false, control := false, name := .alpha }

def eraseControlRight : ProfileState :=
  { core := 2, life := true, control := false, name := .alpha }

/-- Lifecycle observation can relate states that name-aware observation separates. -/
theorem lifecycle_not_nameAware :
    lifecycleProfile.rel lifecycleLeft lifecycleRight ∧
      ¬ nameAwareProfile.rel lifecycleLeft lifecycleRight := by
  change
    (1 = 1 ∧ true = true ∧ false = false) ∧
      ¬ (1 = 1 ∧ ToyKey.alpha = ToyKey.beta)
  decide

/-- Control erasure can relate states that lifecycle observation separates. -/
theorem eraseControl_not_lifecycle :
    eraseControlProfile.rel eraseControlLeft eraseControlRight ∧
      ¬ lifecycleProfile.rel eraseControlLeft eraseControlRight := by
  change
    (2, ToyKey.alpha) = (2, ToyKey.alpha) ∧
      ¬ (2 = 2 ∧ false = true ∧ false = false)
  decide

/-! ## Checked-update fixture -/

def sameStatic (before candidate : Nat × Bool) : Prop :=
  before.1 = candidate.1

instance : DecidableRel sameStatic := fun before candidate ↦
  inferInstanceAs (Decidable (before.1 = candidate.1))

/-! ## Executable report -/

/-- Exact finite outputs for the P5 state, registry, store, and adapter seams. -/
structure StateReport where
  emptyLookup : Option ToyValue
  insertLookup : Option ToyValue
  distinctLookupFramed : Bool
  rawOverwriteUpdated : Bool
  rawOverwriteDomainNodup : Bool
  duplicateFreshInsertRejected : Bool
  freshInsertAccepted : Bool
  lawBreakingCandidateRejected : Bool
  missingLookup : Option ToyValue
  missingEraseRejected : Bool
  presentEraseCapturedValue : Bool
  presentEraseRemovedKey : Bool
  freshInsertEraseRecovered : Bool
  capturedEraseInsertRecovered : Bool
  lifecycleRelatedButNameAwareRejected : Bool
  eraseControlRelatedButLifecycleRejected : Bool
  dependentCoeffectNatLookup : Option Nat
  dependentCoeffectBoolLookup : Option Bool
  checkedUpdateAccepted : Bool
  checkedUpdateRejected : Bool
  deriving DecidableEq, Repr

/-- Evaluate all positive and negative P5 fixtures. -/
def stateReport : StateReport :=
  { emptyLookup := toyApi.lookup toyApi.empty .alpha
    insertLookup := toyApi.lookup insertedToy .alpha
    distinctLookupFramed := decide (toyApi.lookup insertedToy .beta = none)
    rawOverwriteUpdated := decide (toyApi.lookup overwrittenToy .alpha = some .second)
    rawOverwriteDomainNodup := decide (toyApi.domain overwrittenToy).Nodup
    duplicateFreshInsertRejected :=
      match toyExampleFresh with
      | none => true
      | some _ => false
    freshInsertAccepted :=
      match toyExampleFreshKey with
      | none => false
      | some _ => true
    lawBreakingCandidateRejected :=
      decide (¬ (duplicateCandidate.map Prod.fst).Nodup)
    missingLookup := toyApi.lookup toyApi.empty .gamma
    missingEraseRejected :=
      match erasePresent? toyApi toyApi.empty .gamma with
      | none => true
      | some _ => false
    presentEraseCapturedValue :=
      match erasedToy with
      | none => false
      | some (value, _) => value = .second
    presentEraseRemovedKey :=
      match erasedToy with
      | none => false
      | some (_, registry) => toyApi.lookup registry .beta = none
    freshInsertEraseRecovered := sameToyLookups freshThenErase toyApi.empty
    capturedEraseInsertRecovered := sameToyLookups capturedEraseThenInsert toyExample
    lifecycleRelatedButNameAwareRejected :=
      decide (
        lifecycleLeft.core = lifecycleRight.core ∧
          lifecycleLeft.life = lifecycleRight.life ∧
            lifecycleLeft.control = lifecycleRight.control ∧
              lifecycleLeft.name ≠ lifecycleRight.name)
    eraseControlRelatedButLifecycleRejected :=
      decide (
        eraseControlLeft.core = eraseControlRight.core ∧
          eraseControlLeft.name = eraseControlRight.name ∧
            eraseControlLeft.life ≠ eraseControlRight.life)
    dependentCoeffectNatLookup := Coeffect.lookup .natKey depStore
    dependentCoeffectBoolLookup := Coeffect.lookup .boolKey depStore
    checkedUpdateAccepted :=
      decide (
        State.FinmapAdapter.checkedUpdate sameStatic (1, false) (1, true) =
          some (1, true))
    checkedUpdateRejected :=
      decide (
        State.FinmapAdapter.checkedUpdate sameStatic (1, false) (2, false) = none) }

/-- The exact expected output of `stateReport`. -/
def expectedStateReport : StateReport :=
  { emptyLookup := none
    insertLookup := some .first
    distinctLookupFramed := true
    rawOverwriteUpdated := true
    rawOverwriteDomainNodup := true
    duplicateFreshInsertRejected := true
    freshInsertAccepted := true
    lawBreakingCandidateRejected := true
    missingLookup := none
    missingEraseRejected := true
    presentEraseCapturedValue := true
    presentEraseRemovedKey := true
    freshInsertEraseRecovered := true
    capturedEraseInsertRecovered := true
    lifecycleRelatedButNameAwareRejected := true
    eraseControlRelatedButLifecycleRejected := true
    dependentCoeffectNatLookup := some 7
    dependentCoeffectBoolLookup := some true
    checkedUpdateAccepted := true
    checkedUpdateRejected := true }

/-- The finite report matches all intended positive and negative outcomes. -/
theorem stateReport_expected : stateReport = expectedStateReport := by
  decide

end

end STC
