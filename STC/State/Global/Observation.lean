module

public import STC.State.Global
public import STC.State.Observation.Lift

/-!
# Global state observations

The D33 full-state relation is a lifted observation over the positive registry
and coeffect store, closed under the five T01C observation components.
Lifecycle, control-edit, and name observations are separate relation
components; none is silently interchangeable with another.

## Main declarations

* `GlobalObservation`, `StateObs` and the five component projections.
* `stateObs_refl`, `stateObs_symm`, `stateObs_trans`.
* `registryObservation`, `committedObservation`, `observationKit`, and
  `stateObs_eq_lifted`: the concrete D33 instantiation of the T01C
  `ObservationKit`/`liftedStateObs` interface.
-/

universe u

namespace STC.State

@[expose] public section

section GlobalObservation

/-! The concrete D33 kit is uniform-universe: the frozen T01C `ObservationKit`
shares one universe between several of its carriers, which mixed-universe state
families cannot instantiate. The state modules keep mixed universes; only this
kit assembly is uniform. -/

variable {Name : Type u} {Key : Type u} {Value : Type u}
variable {Action : Type u} {Iterator : Type u} {Accumulator : Type u}
variable {Flight : Type u} {Failure : Type u} {Ambient : Type u}
variable [DecidableEq Name] [DecidableEq Key]

local notation "GCell" =>
  FiberCell Name Key Value Action Iterator Accumulator Flight Failure
local notation "GState" =>
  GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient

/-- A complete observation kit for global states. -/
structure GlobalObservation where
  registry : ∀ _name : Name, RelSpec GCell
  coeffects : RelSpec (Finmap (fun _ : Key => Value))
  lifecycle : GState → GState → Prop
  controlEdit : GState → GState → Prop
  names : GState → GState → Prop

local notation "GObs" => GlobalObservation (Name := Name) (Key := Key) (Value := Value)
  (Action := Action) (Iterator := Iterator) (Accumulator := Accumulator)
  (Flight := Flight) (Failure := Failure) (Ambient := Ambient)

/-- D33: lift registry and coeffect observations to the full state carrier. -/
def StateObs (kit : GObs) (left right : GState) : Prop :=
  (∀ name, OptionRel (kit.registry name).rel
      (Finmap.lookup name left.registry) (Finmap.lookup name right.registry)) ∧
    kit.coeffects.rel left.coeffects right.coeffects ∧
      kit.lifecycle left right ∧ kit.controlEdit left right ∧ kit.names left right

theorem stateObs_registry (kit : GObs) {left right : GState}
    (h : StateObs kit left right) (name : Name) :
    OptionRel (kit.registry name).rel (Finmap.lookup name left.registry)
      (Finmap.lookup name right.registry) :=
  h.1 name

theorem stateObs_coeffects (kit : GObs) {left right : GState}
    (h : StateObs kit left right) : kit.coeffects.rel left.coeffects right.coeffects := h.2.1

theorem stateObs_lifecycle (kit : GObs) {left right : GState}
    (h : StateObs kit left right) : kit.lifecycle left right := h.2.2.1

theorem stateObs_controlEdit (kit : GObs) {left right : GState}
    (h : StateObs kit left right) : kit.controlEdit left right := h.2.2.2.1

theorem stateObs_names (kit : GObs) {left right : GState}
    (h : StateObs kit left right) : kit.names left right := h.2.2.2.2

/-- The lifted observation is reflexive when the three bare state components are. -/
theorem stateObs_refl (kit : GObs)
    (hlife : ∀ state : GState, kit.lifecycle state state)
    (hedit : ∀ state : GState, kit.controlEdit state state)
    (hname : ∀ state : GState, kit.names state state) (state : GState) :
    StateObs kit state state := by
  refine ⟨?_, kit.coeffects.refl state.coeffects, hlife state, hedit state, hname state⟩
  intro name
  cases h : Finmap.lookup name state.registry with
  | none => trivial
  | some cell => exact (kit.registry name).refl cell

/-- The lifted observation is symmetric when the three bare state components are. -/
theorem stateObs_symm (kit : GObs)
    (hlife : ∀ {left right : GState}, kit.lifecycle left right → kit.lifecycle right left)
    (hedit : ∀ {left right : GState}, kit.controlEdit left right → kit.controlEdit right left)
    (hname : ∀ {left right : GState}, kit.names left right → kit.names right left)
    {left right : GState} (h : StateObs kit left right) :
    StateObs kit right left := by
  refine ⟨?_, kit.coeffects.symm h.2.1, hlife h.2.2.1, hedit h.2.2.2.1, hname h.2.2.2.2⟩
  intro name
  have hlr := h.1 name
  cases hl : Finmap.lookup name left.registry with
  | none =>
      cases hr : Finmap.lookup name right.registry with
      | none => trivial
      | some _ => simp [OptionRel, hl, hr] at hlr
  | some cellLeft =>
      cases hr : Finmap.lookup name right.registry with
      | none => simp [OptionRel, hl, hr] at hlr
      | some cellRight =>
          exact (kit.registry name).symm (by simpa [OptionRel, hl, hr] using hlr)

/-- The lifted observation is transitive when the three bare state components are. -/
theorem stateObs_trans (kit : GObs)
    (hlife : ∀ {left middle right : GState},
      kit.lifecycle left middle → kit.lifecycle middle right → kit.lifecycle left right)
    (hedit : ∀ {left middle right : GState},
      kit.controlEdit left middle → kit.controlEdit middle right → kit.controlEdit left right)
    (hname : ∀ {left middle right : GState},
      kit.names left middle → kit.names middle right → kit.names left right)
    {left middle right : GState}
    (h₁ : StateObs kit left middle) (h₂ : StateObs kit middle right) :
    StateObs kit left right := by
  refine ⟨?_, kit.coeffects.trans h₁.2.1 h₂.2.1,
    hlife h₁.2.2.1 h₂.2.2.1, hedit h₁.2.2.2.1 h₂.2.2.2.1,
    hname h₁.2.2.2.2 h₂.2.2.2.2⟩
  intro name
  have hlm := h₁.1 name
  have hmr := h₂.1 name
  cases hl : Finmap.lookup name left.registry with
  | none =>
      have hm : Finmap.lookup name middle.registry = none := by
        cases hm0 : Finmap.lookup name middle.registry with
        | none => rfl
        | some _ => simp [OptionRel, hl, hm0] at hlm
      rw [hm] at hmr
      cases hr : Finmap.lookup name right.registry with
      | none => trivial
      | some _ => simp [OptionRel, hr] at hmr
  | some cellLeft =>
      cases hm : Finmap.lookup name middle.registry with
      | none => simp [OptionRel, hl, hm] at hlm
      | some cellMiddle =>
          cases hr : Finmap.lookup name right.registry with
          | none => simp [OptionRel, hm, hr] at hmr
          | some cellRight =>
              exact (kit.registry name).trans
                (by simpa [OptionRel, hl, hm] using hlm)
                (by simpa [OptionRel, hm, hr] using hmr)

/-! ### The T01C observation-kit instantiation -/

/-- The registry component of the T01C kit: pointwise option-relator observation. -/
def registryObservation (kit : GObs) :
    RegistryObservation (Registry := Finmap (fun _ : Name => GCell)) where
  rel left right := ∀ name, OptionRel (kit.registry name).rel
    (Finmap.lookup name left) (Finmap.lookup name right)
  refl := by
    intro registry name
    cases h : Finmap.lookup name registry with
    | none => trivial
    | some cell => exact (kit.registry name).refl cell
  symm := by
    intro left right h name
    have hn := h name
    cases hl : Finmap.lookup name left with
    | none =>
        cases hr : Finmap.lookup name right with
        | none => trivial
        | some _ => simp [OptionRel, hl, hr] at hn
    | some cellLeft =>
        cases hr : Finmap.lookup name right with
        | none => simp [OptionRel, hl, hr] at hn
        | some cellRight => exact (kit.registry name).symm (by simpa [OptionRel, hl, hr] using hn)
  trans := by
    intro left middle right h₁ h₂ name
    have hlm := h₁ name
    have hmr := h₂ name
    cases hl : Finmap.lookup name left with
    | none =>
        have hm : Finmap.lookup name middle = none := by
          cases hm0 : Finmap.lookup name middle with
          | none => rfl
          | some _ => simp [OptionRel, hl, hm0] at hlm
        rw [hm] at hmr
        cases hr : Finmap.lookup name right with
        | none => trivial
        | some _ => simp [OptionRel, hr] at hmr
    | some cellLeft =>
        cases hm : Finmap.lookup name middle with
        | none => simp [OptionRel, hl, hm] at hlm
        | some cellMiddle =>
            cases hr : Finmap.lookup name right with
            | none => simp [OptionRel, hm, hr] at hmr
            | some cellRight =>
                exact (kit.registry name).trans
                  (by simpa [OptionRel, hl, hm] using hlm)
                  (by simpa [OptionRel, hm, hr] using hmr)

/-- The committed-store component of the T01C kit is the explicit store relation. -/
def committedObservation (kit : GObs) :
    CommittedObservation (Store := Finmap (fun _ : Key => Value)) where
  rel := kit.coeffects.rel
  refl := kit.coeffects.refl
  symm := kit.coeffects.symm
  trans := kit.coeffects.trans

/-- The concrete D33 kit instantiating the T01C `ObservationKit` interface. -/
def observationKit (kit : GObs) :
    ObservationKit (Registry := Finmap (fun _ : Name => GCell))
      (Store := Finmap (fun _ : Key => Value))
      (Life := GState) (Edit := GState) (Name := GState) :=
  { registry := registryObservation kit
    committed := committedObservation kit
    lifecycle := kit.lifecycle
    controlEdit := kit.controlEdit
    names := kit.names }

/-- `StateObs` is exactly the T01C lifted observation over the concrete
projections: the D33 relation instantiates the generic observation interface. -/
theorem stateObs_eq_lifted (kit : GObs) {left right : GState} :
    StateObs kit left right ↔
      liftedStateObs (observationKit kit)
        (fun state : GState => state.registry) (fun state => state.coeffects)
        (fun state => state) (fun state => state) (fun state => state) left right := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end GlobalObservation

end

end STC.State
