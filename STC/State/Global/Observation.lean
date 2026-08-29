module

public import STC.State.Global
public import STC.State.Observation.Lift

/-!
# Global state observations

The D33-style full-state relation is a lifted observation over the positive
registry and coeffect store. Lifecycle, control-edit, and name observations are
separate relation components.
-/

universe u v w x

namespace STC.State

@[expose] public section

section GlobalObservation

variable {Name : Type u} {Key : Type v} {Value : Type w}
variable {Action : Type u} {Iterator : Type v} {Accumulator : Type w}
variable {Flight : Type u} {Failure : Type v} {Ambient : Type x}
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

/-- Lift registry and coeffect observations to the full state carrier. -/
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

end GlobalObservation

end

end STC.State
