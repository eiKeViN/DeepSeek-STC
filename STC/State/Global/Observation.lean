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

/-- A complete observation kit for global states. -/
structure GlobalObservation where
  registry : ∀ _name : Name, RelSpec (FiberCell Name Key Value Action Iterator Accumulator Flight Failure)
  coeffects : RelSpec (Finmap (fun _ : Key => Value))
  lifecycle : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient →
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  controlEdit : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient →
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop
  names : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient →
    GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient → Prop

/-- Lift registry and coeffect observations to the full state carrier. -/
def StateObs (kit : GlobalObservation (Name := Name) (Key := Key) (Value := Value)
    (Action := Action) (Iterator := Iterator) (Accumulator := Accumulator)
    (Flight := Flight) (Failure := Failure) (Ambient := Ambient))
    (left right : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient) : Prop :=
  (∀ name, OptionRel (kit.registry name).rel
      (Finmap.lookup name left.registry) (Finmap.lookup name right.registry)) ∧
    kit.coeffects.rel left.coeffects right.coeffects ∧
      kit.lifecycle left right ∧ kit.controlEdit left right ∧ kit.names left right

theorem stateObs_registry (kit : GlobalObservation (Name := Name) (Key := Key) (Value := Value)
    (Action := Action) (Iterator := Iterator) (Accumulator := Accumulator)
    (Flight := Flight) (Failure := Failure) (Ambient := Ambient))
    {left right : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient}
    (h : StateObs kit left right) (name : Name) :
    OptionRel (kit.registry name).rel (Finmap.lookup name left.registry) (Finmap.lookup name right.registry) := h.1 name

theorem stateObs_coeffects (kit : GlobalObservation (Name := Name) (Key := Key) (Value := Value)
    (Action := Action) (Iterator := Iterator) (Accumulator := Accumulator)
    (Flight := Flight) (Failure := Failure) (Ambient := Ambient))
    {left right : GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient}
    (h : StateObs kit left right) : kit.coeffects.rel left.coeffects right.coeffects := h.2.1

end GlobalObservation

end

end STC.State
