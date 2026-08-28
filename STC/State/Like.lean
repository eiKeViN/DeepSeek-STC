import STC.Foundation.Relation

/-!
# Abstract state projections

This module defines the small state projection and explicit observation-profile
contract used by P5. Validity, lifecycle, provider, and transition invariants
remain outside `StateLike`.

## Main declarations

* `StateLike`: a single projection from an abstract state.
* `ObservationProfile`: a supplied state relation, observed relation, and a
  proof that the projection respects them.
* `ObservationProfile.exact`: the canonical exact-pullback profile.
-/

universe u v

namespace STC

variable {S : Type u} {O : Type v}

/-- A state carrier equipped with one explicit observation projection. -/
structure StateLike (S : Type u) (O : Type v) where
  project : S → O

/--
An explicit observation profile.

The state relation may be supplied independently of the observation pullback,
but the projection must visibly respect it. Use `ObservationProfile.exact`
when the state relation is exactly the induced pullback.
-/
structure ObservationProfile (S : Type u) (O : Type v) extends StateLike S O where
  stateRel : RelSpec S
  obsRel : RelSpec O
  project_respects : RespectsOn stateRel.rel obsRel.rel project

namespace ObservationProfile

/-- The relation induced by pulling an observation relation back along its projection. -/
def inducedRel (profile : ObservationProfile S O) : RelSpec S :=
  pullbackRelSpec profile.project profile.obsRel

/-- Construct a profile whose state relation is exactly the observation pullback. -/
def exact (project : S → O) (obsRel : RelSpec O) : ObservationProfile S O where
  project := project
  stateRel := pullbackRelSpec project obsRel
  obsRel := obsRel
  project_respects := by
    intro left right h
    exact h

/-- The state relation of `exact` is definitionally the induced pullback. -/
theorem exact_stateRel (project : S → O) (obsRel : RelSpec O) :
    (exact project obsRel).stateRel = pullbackRelSpec project obsRel :=
  rfl

/-- Equality observation is the exact pullback of equality along the projection. -/
def exactEquality (project : S → O) : ObservationProfile S O :=
  exact project (equality O)

end ObservationProfile

end STC
