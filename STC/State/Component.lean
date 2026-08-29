module

public import STC.Core.Coeffect
public import STC.State.Positive

/-!
# Positive component data

Components contain requirements, provisions, and executable codes only. Their
denotations and frame laws are supplied by an external interpretation profile.
-/

universe u v w

namespace STC.State

@[expose] public section

section Component

variable {Key : Type u} {Value : Type v} {Action : Type w} {Iterator : Type u}
variable {Accumulator : Type v} {Flight : Type w} {Failure : Type u}

/-- Data-only component declaration for one logical key. -/
structure Component (Key : Type u) (Value : Type v) (Action : Type w)
    (Iterator : Type u) (Accumulator : Type v) (Flight : Type w) (Failure : Type u) where
  key : Key
  requires : Finset Key
  provides : Finset Key
  actionCode : Action
  iteratorCode : Iterator
  accumulatorCode : Accumulator
  flightCode : Flight
  failureCode : Failure

/-- External semantic interpretation for a component code. -/
structure ComponentSemantics (State : Type u) (Value : Type v) (Action : Type w)
    (Iterator : Type u) (Accumulator : Type v) (Flight : Type u) (Failure : Type v) where
  action : Action → State → Option State
  iterator : Iterator → State → Option State
  accumulator : Accumulator → State → Option State
  flight : Flight → State → Option State
  failure : Failure → State → Option State
  noWriteOutside : Prop
  action_frame : Prop
  iterator_frame : Prop
  inverse_law : Prop
  relation_respect : Prop
  rank_law : Prop
  continuation_stable : Prop

/-- A component's declared provisions are disjoint from foreign writes under a
supplied local footprint relation. -/
def NoWriteOutsideProvision (component : Component Key Value Action Iterator Accumulator Flight Failure)
    (written : Finset Key) : Prop :=
  written ⊆ component.provides

theorem noWriteOutsideProvision_refl
    (component : Component Key Value Action Iterator Accumulator Flight Failure) :
    NoWriteOutsideProvision component component.provides := by
  intro key h
  exact h

end Component

end

end STC.State
