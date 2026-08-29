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
  undo : State → Option State
  observes : State → State → Prop
  writesWithinProvision : State → State → Prop
  continuationStable : State → State → Prop
  rank : State → Nat
  noWriteOutside : ∀ {code before after}, action code before = some after →
    writesWithinProvision before after
  action_frame : ∀ {code before after}, action code before = some after →
    observes before after
  iterator_frame : ∀ {code before after}, iterator code before = some after →
    observes before after
  inverse_law : ∀ {code before after}, action code before = some after →
    undo after = some before
  relation_respect : ∀ {code left right left' right'}, observes left right →
    action code left = some left' → action code right = some right' → observes left' right'
  rank_law : ∀ {code before after}, iterator code before = some after →
    rank after < rank before
  continuation_stable : ∀ {code before after}, flight code before = some after →
    continuationStable before after

/-- A component's declared provisions are disjoint from foreign writes under a
supplied local footprint relation. -/
def NoWriteOutsideProvision
    (component : Component Key Value Action Iterator Accumulator Flight Failure)
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
