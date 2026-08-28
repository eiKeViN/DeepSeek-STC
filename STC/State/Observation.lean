module

public import STC.State.Like

/-!
# Explicit state-observation boundaries

This module keeps core observation, lifecycle observation, control erasure,
and name-aware observation as distinct relation values. It also records the
one-way projection contract between a fiber registry and its derived coeffect
view without equating their carriers or domains.

## Main declarations

* `CoreStateObs`, `LifecycleObs`, `EraseControl`, and `NameAwareObs`.
* `StoreRegistryBoundary`: the explicit store/registry observation seam.
-/

universe u v w x y z

namespace STC

@[expose] public section

section ObservationRelations

variable {S : Type u} {O : Type v} {P : Type w}
variable {Core : Type x} {Life : Type y} {Control : Type z} {Erased : Type y} {Names : Type z}

/-- Conjoin two explicit equivalence specifications on the same carrier. -/
def RelSpec.conj (R T : RelSpec S) : RelSpec S where
  rel left right := R.rel left right ∧ T.rel left right
  refl state := ⟨R.refl state, T.refl state⟩
  symm h := ⟨R.symm h.1, T.symm h.2⟩
  trans h₁ h₂ := ⟨R.trans h₁.1 h₂.1, T.trans h₁.2 h₂.2⟩

/-- Observe only the explicitly selected core projection. -/
def CoreStateObs (state : StateLike S Core) (coreRel : RelSpec Core) : RelSpec S :=
  pullbackRelSpec state.project coreRel

/-- Combine core, lifecycle, and control-sensitive observation. -/
def LifecycleObs (core : RelSpec S) (life : ObservationProfile S Life)
    (control : ObservationProfile S Control) : RelSpec S :=
  RelSpec.conj core (RelSpec.conj life.stateRel control.stateRel)

/-- Select an explicit control-erasing observation profile. -/
def EraseControl (erased : ObservationProfile S Erased) : RelSpec S :=
  erased.stateRel

/-- Combine core observation with an explicit name-bearing view. -/
def NameAwareObs (core : RelSpec S) (names : ObservationProfile S Names) : RelSpec S :=
  RelSpec.conj core names.stateRel

/-- Nested pullbacks agree with pullback along the composed projection. -/
theorem pullback_comp (project : S → O) (observe : O → P) (relation : RelSpec P) :
    (pullbackRelSpec project (pullbackRelSpec observe relation)).rel =
      (pullbackRelSpec (observe ∘ project) relation).rel := by
  rfl

/-- Lifecycle observation exposes all three constituent relations. -/
theorem lifecycleObs_iff (core : RelSpec S) (life : ObservationProfile S Life)
    (control : ObservationProfile S Control) (left right : S) :
    (LifecycleObs core life control).rel left right ↔
      core.rel left right ∧ life.stateRel.rel left right ∧ control.stateRel.rel left right := by
  rfl

/-- Lifecycle observation implies its core component. -/
theorem lifecycleObs_implies_core (core : RelSpec S) (life : ObservationProfile S Life)
    (control : ObservationProfile S Control) {left right : S}
    (h : (LifecycleObs core life control).rel left right) : core.rel left right :=
  h.1

/-- Lifecycle observation implies its lifecycle component. -/
theorem lifecycleObs_implies_lifecycle (core : RelSpec S) (life : ObservationProfile S Life)
    (control : ObservationProfile S Control) {left right : S}
    (h : (LifecycleObs core life control).rel left right) : life.stateRel.rel left right :=
  h.2.1

/-- Lifecycle observation implies its control-sensitive component. -/
theorem lifecycleObs_implies_control (core : RelSpec S) (life : ObservationProfile S Life)
    (control : ObservationProfile S Control) {left right : S}
    (h : (LifecycleObs core life control).rel left right) : control.stateRel.rel left right :=
  h.2.2

/-- Name-aware observation exposes its core and name-bearing components. -/
theorem nameAwareObs_iff (core : RelSpec S) (names : ObservationProfile S Names)
    (left right : S) :
    (NameAwareObs core names).rel left right ↔
      core.rel left right ∧ names.stateRel.rel left right := by
  rfl

/-- Name-aware observation implies its core component. -/
theorem nameAwareObs_implies_core (core : RelSpec S) (names : ObservationProfile S Names)
    {left right : S} (h : (NameAwareObs core names).rel left right) : core.rel left right :=
  h.1

/-- Name-aware observation implies its name-bearing component. -/
theorem nameAwareObs_implies_names (core : RelSpec S) (names : ObservationProfile S Names)
    {left right : S} (h : (NameAwareObs core names).rel left right) :
    names.stateRel.rel left right :=
  h.2

end ObservationRelations

/-! ## Store/registry boundary -/

section StoreRegistryBoundary

/--
An explicit one-way projection from a fiber registry to its derived coeffect
view. This contract does not equate registry keys with coeffect keys and makes
no provider-uniqueness or fold-order claim.
-/
structure StoreRegistryBoundary (Registry : Type u) (Store : Type v) where
  registryObs : RelSpec Registry
  storeObs : RelSpec Store
  activeStore : Registry → Store
  activeStore_respects : RespectsOn registryObs.rel storeObs.rel activeStore

end StoreRegistryBoundary

end

end STC
