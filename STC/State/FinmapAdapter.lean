module

public import STC.State.CoeffectStore
public import STC.State.Observation
public import STC.State.RegistryLike

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
* `ProviderProvenance`: well-formed-relative sound, complete, and unique provider selection.
* `StaticProjection` and `checkedUpdate`: an explicit static-field gate.
* `StateAbstraction`: one-way observation evidence for valid raw states.
-/

universe u v w

namespace STC.State.FinmapAdapter

@[expose] public section

section RawState

/-- The positive ADR-03 raw carrier: ambient data plus an abstract registry carrier. -/
structure RawState (Ambient : Type u) (Registry : Type v) where
  ambient : Ambient
  registry : Registry

end RawState

section WellFormedness

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

end WellFormedness

section Providers

/--
Provider provenance as an explicit R0 contract.

The fields expose well-formed-relative soundness, completeness, and uniqueness
rather than deriving a provider by hidden classical choice. No behavior is
prescribed for malformed raw states.
-/
structure ProviderProvenance (Raw : Type u) (Key : Type v) (Provider : Type w)
    (coreWF : Raw → Prop) where
  providesNow : Raw → Provider → Key → Prop
  providerOf : Raw → Key → Option Provider
  provider_sound : ∀ {state key provider},
    coreWF state → providerOf state key = some provider → providesNow state provider key
  provider_complete : ∀ {state key provider},
    coreWF state → providesNow state provider key → providerOf state key = some provider
  provider_unique : ∀ {state key left right},
    coreWF state → providesNow state left key → providesNow state right key → left = right

/-- Provider choice agrees exactly with the provider relation on well-formed states. -/
theorem ProviderProvenance.provider_iff
    {Raw : Type u} {Key : Type v} {Provider : Type w} {coreWF : Raw → Prop}
    (provenance : ProviderProvenance Raw Key Provider coreWF)
    {state : Raw} {key : Key} {provider : Provider} (hWF : coreWF state) :
    provenance.providerOf state key = some provider ↔
      provenance.providesNow state provider key :=
  ⟨provenance.provider_sound hWF, provenance.provider_complete hWF⟩

end Providers

section StaticUpdates

/-- The declared projection of a raw state onto fields that updates must preserve. -/
structure StaticProjection (Raw : Type u) (Static : Type v) where
  project : Raw → Static

/-- Accept a candidate update exactly when its declared static projection is unchanged. -/
def checkedUpdate {Raw : Type u} {Static : Type v}
    (projection : StaticProjection Raw Static) [DecidableEq Static]
    (before candidate : Raw) : Option Raw :=
  if projection.project before = projection.project candidate then some candidate else none

/-- A checked update succeeds exactly when the static projection is unchanged. -/
theorem checkedUpdate_eq_some_iff {Raw : Type u} {Static : Type v}
    (projection : StaticProjection Raw Static) [DecidableEq Static]
    (before candidate : Raw) :
    checkedUpdate projection before candidate = some candidate ↔
      projection.project before = projection.project candidate := by
  simp [checkedUpdate]

/-- A checked update fails exactly when the static projection changes. -/
theorem checkedUpdate_eq_none_iff {Raw : Type u} {Static : Type v}
    (projection : StaticProjection Raw Static) [DecidableEq Static]
    (before candidate : Raw) :
    checkedUpdate projection before candidate = none ↔
      projection.project before ≠ projection.project candidate := by
  simp [checkedUpdate]

end StaticUpdates

section Abstraction

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

end Abstraction

end

end STC.State.FinmapAdapter
