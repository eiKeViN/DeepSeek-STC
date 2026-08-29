module

public import STC.Foundation.Relation.Transport
public import STC.State.Observation
public import STC.State.Positive

/-!
# Parametric state-observation lifts

The observation kit used by the global theorems names registry, committed-store,
lifecycle, control-edit, and name observations independently.
-/

universe u v w x

namespace STC.State

@[expose] public section

section Observation

variable {S : Type u} {Registry : Type v} {Store : Type w}
variable {Life : Type x} {Edit : Type u} {Name : Type v}

/-- Registry observation is supplied as a relation rather than inferred from
carrier equality. -/
structure RegistryObservation where
  rel : Registry → Registry → Prop
  refl : ∀ r, rel r r
  symm : ∀ {r s}, rel r s → rel s r
  trans : ∀ {r s t}, rel r s → rel s t → rel r t

/-- Committed-store observation is an independent relation boundary. -/
structure CommittedObservation where
  rel : Store → Store → Prop
  refl : ∀ s, rel s s
  symm : ∀ {s t}, rel s t → rel t s
  trans : ∀ {s t u}, rel s t → rel t u → rel s u

/-- Lifecycle and control-edit/name observations remain separately selectable. -/
structure ObservationKit where
  registry : RegistryObservation (Registry := Registry)
  committed : CommittedObservation (Store := Store)
  lifecycle : Life → Life → Prop
  controlEdit : Edit → Edit → Prop
  names : Name → Name → Prop

/-- A lifted state observation from explicitly chosen projections. -/
def liftedStateObs (kit : ObservationKit (Registry := Registry) (Store := Store)
    (Life := Life) (Edit := Edit) (Name := Name))
    (registry : S → Registry) (committed : S → Store)
    (life : S → Life) (edit : S → Edit) (names : S → Name) (left right : S) : Prop :=
  kit.registry.rel (registry left) (registry right) ∧
    kit.committed.rel (committed left) (committed right) ∧
      kit.lifecycle (life left) (life right) ∧
        kit.controlEdit (edit left) (edit right) ∧ kit.names (names left) (names right)

theorem liftedStateObs_registry (kit : ObservationKit (Registry := Registry) (Store := Store)
    (Life := Life) (Edit := Edit) (Name := Name))
    (registry : S → Registry) (committed : S → Store)
    (life : S → Life) (edit : S → Edit) (names : S → Name)
    {left right : S} (h : liftedStateObs kit registry committed life edit names left right) :
    kit.registry.rel (registry left) (registry right) := h.1

theorem liftedStateObs_committed (kit : ObservationKit (Registry := Registry) (Store := Store)
    (Life := Life) (Edit := Edit) (Name := Name))
    (registry : S → Registry) (committed : S → Store)
    (life : S → Life) (edit : S → Edit) (names : S → Name)
    {left right : S} (h : liftedStateObs kit registry committed life edit names left right) :
    kit.committed.rel (committed left) (committed right) := h.2.1

end Observation

end

end STC.State
