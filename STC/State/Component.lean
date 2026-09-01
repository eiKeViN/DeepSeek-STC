module

public import STC.Core.Coeffect
public import STC.State.Positive

/-!
# Positive component data

Components contain requirements, provisions, and executable codes only. Their
denotations and frame laws are supplied by an external interpretation profile.
-/

universe u v w x y z

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

/-- One executed iterator stage. `yield` carries the after-state, the yielded
inverse, and the continuation; `halt` the after-state and the final inverse;
`raise` the state at which the stage failed and the failure payload. -/
inductive StageResult (State : Type u) (Iterator : Type v) (Accumulator : Type w)
    (Failure : Type x) where
  | yield (after : State) (inverse : Accumulator) (next : Iterator)
  | halt (after : State) (inverse : Accumulator)
  | raise (before : State) (failure : Failure)

namespace StageResult

/-- The state reached (or held, for a raise) by one stage execution. -/
def state {State : Type u} {Iterator : Type v} {Accumulator : Type w} {Failure : Type x} :
    StageResult State Iterator Accumulator Failure → State
  | .yield after _ _ => after
  | .halt after _ => after
  | .raise before _ => before

/-- The yielded/final inverse, present exactly for non-raising stages. -/
def inverse? {State : Type u} {Iterator : Type v} {Accumulator : Type w} {Failure : Type x} :
    StageResult State Iterator Accumulator Failure → Option Accumulator
  | .yield _ inverse _ => some inverse
  | .halt _ inverse => some inverse
  | .raise _ _ => none

/-- The failure payload, present exactly for raising stages. -/
def failure? {State : Type u} {Iterator : Type v} {Accumulator : Type w} {Failure : Type x} :
    StageResult State Iterator Accumulator Failure → Option Failure
  | .yield _ _ _ => none
  | .halt _ _ => none
  | .raise _ failure => some failure

end StageResult

/-- External semantic interpretation for a component code. Each code family
carries its own universe so the profile instantiates over mixed-universe
carriers like `GlobalState`. -/
structure ComponentSemantics (State : Type u) (Value : Type v) (Action : Type w)
    (Iterator : Type x) (Accumulator : Type y) (Flight : Type z) (Failure : Type x) where
  action : Action → State → Option State
  stage : Iterator → State → Option (StageResult State Iterator Accumulator Failure)
  composeInverse : Accumulator → Accumulator → Accumulator
  identityAccumulator : Accumulator
  accumulator : Accumulator → State → Option State
  launch : State → Option Flight
  flight : Flight → State → Option State
  failure : Failure → State → Option State
  undo : State → Option State
  observes : State → State → Prop
  writesWithinProvision : State → State → Prop
  continuationStable : State → State → Prop
  rank : State → Nat
  accumulatorFrame : Accumulator → State → State → Prop
  noWriteOutside : ∀ {code before after}, action code before = some after →
    writesWithinProvision before after
  action_frame : ∀ {code before after}, action code before = some after →
    observes before after
  stage_frame : ∀ {code before result}, stage code before = some result →
    observes before (StageResult.state result)
  inverse_law : ∀ {code before after}, action code before = some after →
    undo after = some before
  stage_inverse : ∀ {code before result inverse},
    stage code before = some result → result.inverse? = some inverse →
      accumulator inverse (StageResult.state result) = some before
  relation_respect : ∀ {code left right left' right'}, observes left right →
    action code left = some left' → action code right = some right' → observes left' right'
  rank_law : ∀ {code before result}, stage code before = some result →
    result.failure? = none → rank (StageResult.state result) < rank before
  continuation_stable : ∀ {code before after}, flight code before = some after →
    continuationStable before after
  flight_frame : ∀ {code before after}, flight code before = some after →
    observes before after
  failure_frame : ∀ {code before after}, failure code before = some after →
    observes before after
  composeInverse_law : ∀ {a b before mid after}, accumulator b before = some mid →
    accumulator a mid = some after → accumulator (composeInverse a b) before = some after
  identityAccumulator_law : ∀ state, accumulator identityAccumulator state = some state
  accumulator_frame : ∀ {code before after}, accumulator code before = some after →
    accumulatorFrame code before after

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
