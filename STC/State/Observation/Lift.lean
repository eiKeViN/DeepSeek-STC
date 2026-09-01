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

theorem liftedStateObs_lifecycle (kit : ObservationKit (Registry := Registry) (Store := Store)
    (Life := Life) (Edit := Edit) (Name := Name))
    (registry : S → Registry) (committed : S → Store)
    (life : S → Life) (edit : S → Edit) (names : S → Name)
    {left right : S} (h : liftedStateObs kit registry committed life edit names left right) :
    kit.lifecycle (life left) (life right) := h.2.2.1

theorem liftedStateObs_controlEdit (kit : ObservationKit (Registry := Registry) (Store := Store)
    (Life := Life) (Edit := Edit) (Name := Name))
    (registry : S → Registry) (committed : S → Store)
    (life : S → Life) (edit : S → Edit) (names : S → Name)
    {left right : S} (h : liftedStateObs kit registry committed life edit names left right) :
    kit.controlEdit (edit left) (edit right) := h.2.2.2.1

theorem liftedStateObs_names (kit : ObservationKit (Registry := Registry) (Store := Store)
    (Life := Life) (Edit := Edit) (Name := Name))
    (registry : S → Registry) (committed : S → Store)
    (life : S → Life) (edit : S → Edit) (names : S → Name)
    {left right : S} (h : liftedStateObs kit registry committed life edit names left right) :
    kit.names (names left) (names right) := h.2.2.2.2

/-- The lifted observation is reflexive when the three bare component relations are. -/
theorem liftedStateObs_refl (kit : ObservationKit (Registry := Registry) (Store := Store)
    (Life := Life) (Edit := Edit) (Name := Name))
    (hlife : ∀ l : Life, kit.lifecycle l l) (hedit : ∀ e : Edit, kit.controlEdit e e)
    (hname : ∀ n : Name, kit.names n n)
    (registry : S → Registry) (committed : S → Store)
    (life : S → Life) (edit : S → Edit) (names : S → Name) (state : S) :
    liftedStateObs kit registry committed life edit names state state := by
  exact ⟨kit.registry.refl (registry state), kit.committed.refl (committed state),
    hlife (life state), hedit (edit state), hname (names state)⟩

/-- The lifted observation is symmetric when the three bare component relations are. -/
theorem liftedStateObs_symm (kit : ObservationKit (Registry := Registry) (Store := Store)
    (Life := Life) (Edit := Edit) (Name := Name))
    (hlife : ∀ {l r : Life}, kit.lifecycle l r → kit.lifecycle r l)
    (hedit : ∀ {l r : Edit}, kit.controlEdit l r → kit.controlEdit r l)
    (hname : ∀ {l r : Name}, kit.names l r → kit.names r l)
    (registry : S → Registry) (committed : S → Store)
    (life : S → Life) (edit : S → Edit) (names : S → Name)
    {left right : S} (h : liftedStateObs kit registry committed life edit names left right) :
    liftedStateObs kit registry committed life edit names right left := by
  exact ⟨kit.registry.symm h.1, kit.committed.symm h.2.1,
    hlife h.2.2.1, hedit h.2.2.2.1, hname h.2.2.2.2⟩

/-- The lifted observation is transitive when the three bare component relations are. -/
theorem liftedStateObs_trans (kit : ObservationKit (Registry := Registry) (Store := Store)
    (Life := Life) (Edit := Edit) (Name := Name))
    (hlife : ∀ {l m r : Life}, kit.lifecycle l m → kit.lifecycle m r → kit.lifecycle l r)
    (hedit : ∀ {l m r : Edit}, kit.controlEdit l m → kit.controlEdit m r → kit.controlEdit l r)
    (hname : ∀ {l m r : Name}, kit.names l m → kit.names m r → kit.names l r)
    (registry : S → Registry) (committed : S → Store)
    (life : S → Life) (edit : S → Edit) (names : S → Name)
    {left middle right : S}
    (h₁ : liftedStateObs kit registry committed life edit names left middle)
    (h₂ : liftedStateObs kit registry committed life edit names middle right) :
    liftedStateObs kit registry committed life edit names left right := by
  exact ⟨kit.registry.trans h₁.1 h₂.1, kit.committed.trans h₁.2.1 h₂.2.1,
    hlife h₁.2.2.1 h₂.2.2.1, hedit h₁.2.2.2.1 h₂.2.2.2.1,
    hname h₁.2.2.2.2 h₂.2.2.2.2⟩

end Observation

end

end STC.State
