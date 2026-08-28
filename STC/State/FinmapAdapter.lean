import STC.State.CoeffectStore
import STC.State.Observation
import STC.State.RegistryLike

/-!
# ADR-03 state-side Finmap adapter

This module exposes the P5 one-way R0 contract toward the positive ADR-03
state architecture. It records raw state, visible well-formedness components,
provider provenance, and checked static updates without importing historical
spikes or claiming concrete transition preservation.

`STC.State.FinmapAdapter` is deliberately state-side. The `STC.Adapter`
namespace remains available for the later concrete-to-abstract runtime seam.

## Main declarations

* `RawState`, `CoreWFSpec`, `BoundaryWFSpec`, and `ValidState`.
* `ProviderProvenance`: sound, complete, and unique provider selection.
* `checkedUpdate`: an explicit static-field gate.
* `StateAbstraction`: one-way observation evidence for valid raw states.
-/

universe u v w

namespace STC.State.FinmapAdapter

/-- The positive ADR-03 raw carrier: ambient data plus an abstract registry carrier. -/
structure RawState (Ambient Registry : Type u) where
  ambient : Ambient
  registry : Registry

/-- The seven state-local obligations fixed by the ADR-03 closure packet. -/
structure CoreWFSpec (Raw : Type u) where
  parentClosed : Raw → Prop
  parentAcyclic : Raw → Prop
  tableConfined : Raw → Prop
  provisionDisjoint : Raw → Prop
  lifecycleCoherent : Raw → Prop
  committedViewClosed : Raw → Prop
  committedProvidersClosed : Raw → Prop

/-- Core well-formedness keeps every accepted state invariant separately visible. -/
def CoreWellFormed {Raw : Type u} (spec : CoreWFSpec Raw) (state : Raw) : Prop :=
  spec.parentClosed state ∧
    spec.parentAcyclic state ∧
      spec.tableConfined state ∧
        spec.provisionDisjoint state ∧
          spec.lifecycleCoherent state ∧
            spec.committedViewClosed state ∧ spec.committedProvidersClosed state

/-- Root and declaration obligations remain independent of core well-formedness. -/
structure BoundaryWFSpec (Raw : Type u) where
  rootSpec : Raw → Prop
  declarationSpec : Raw → Prop

/-- Extend core well-formedness with the explicit boundary obligations. -/
def WellFormed {Raw : Type u} (core : CoreWFSpec Raw) (boundary : BoundaryWFSpec Raw)
    (state : Raw) : Prop :=
  CoreWellFormed core state ∧ boundary.rootSpec state ∧ boundary.declarationSpec state

/-- A proof-carrying valid-state view; raw states remain available at failure boundaries. -/
abbrev ValidState {Raw : Type u} (core : CoreWFSpec Raw) (boundary : BoundaryWFSpec Raw) :=
  { state : Raw // WellFormed core boundary state }

/--
Provider provenance as an explicit R0 contract.

The fields expose soundness, well-formed completeness, and uniqueness rather
than deriving a provider by hidden classical choice.
-/
structure ProviderProvenance (Raw Key Provider : Type u) (coreWF : Raw → Prop) where
  providesNow : Raw → Provider → Key → Prop
  providerOf : Raw → Key → Option Provider
  provider_sound : ∀ {state key provider},
    providerOf state key = some provider → providesNow state provider key
  provider_complete : ∀ {state key provider},
    coreWF state → providesNow state provider key → providerOf state key = some provider
  provider_unique : ∀ {state key left right},
    coreWF state → providesNow state left key → providesNow state right key → left = right

/-- Accept a candidate update exactly when its declared static relation holds. -/
def checkedUpdate {Raw : Type u} (sameStatic : Raw → Raw → Prop)
    [DecidableRel sameStatic] (before candidate : Raw) : Option Raw :=
  if sameStatic before candidate then some candidate else none

/-- A checked update succeeds exactly when the static relation holds. -/
theorem checkedUpdate_eq_some_iff {Raw : Type u} (sameStatic : Raw → Raw → Prop)
    [DecidableRel sameStatic] (before candidate : Raw) :
    checkedUpdate sameStatic before candidate = some candidate ↔ sameStatic before candidate := by
  simp [checkedUpdate]

/-- A checked update fails exactly when the static relation does not hold. -/
theorem checkedUpdate_eq_none_iff {Raw : Type u} (sameStatic : Raw → Raw → Prop)
    [DecidableRel sameStatic] (before candidate : Raw) :
    checkedUpdate sameStatic before candidate = none ↔ ¬ sameStatic before candidate := by
  simp [checkedUpdate]

/--
One-way R0 abstraction into an abstract state relation.

Constructing this record for a concrete carrier is the outstanding admission
obligation; the record type itself proves no Cordis refinement claim.
-/
structure StateAbstraction (Raw : Type u) (Abstract : Type v) (Core : Type w)
    (wellFormed : Raw → Prop) where
  abstract : { state : Raw // wellFormed state } → Abstract
  rawCore : Raw → Core
  abstractCore : Abstract → Core
  coreRel : RelSpec Core
  observes : ∀ state, coreRel.rel (abstractCore (abstract state)) (rawCore state)

end STC.State.FinmapAdapter
