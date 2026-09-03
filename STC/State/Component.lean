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
`raise` carries only the current error — the boundary and the accumulated
prefix are supplied by the `FailureFromStage` bridge of the semantics, never
by the stage itself. -/
inductive StageResult (State : Type u) (Iterator : Type v) (Accumulator : Type w)
    (Failure : Type x) where
  | yield (after : State) (inverse : Accumulator) (next : Iterator)
  | halt (after : State) (inverse : Accumulator)
  | raise (error : Failure)

namespace StageResult

/-- The state reached by a successful stage; `none` for a raise. -/
def state? {State : Type u} {Iterator : Type v} {Accumulator : Type w} {Failure : Type x} :
    StageResult State Iterator Accumulator Failure → Option State
  | .yield after _ _ => some after
  | .halt after _ => some after
  | .raise _ => none

/-- The yielded/final inverse, present exactly for non-raising stages. -/
def inverse? {State : Type u} {Iterator : Type v} {Accumulator : Type w} {Failure : Type x} :
    StageResult State Iterator Accumulator Failure → Option Accumulator
  | .yield _ inverse _ => some inverse
  | .halt _ inverse => some inverse
  | .raise _ => none

/-- The failure payload, present exactly for raising stages. -/
def failure? {State : Type u} {Iterator : Type v} {Accumulator : Type w} {Failure : Type x} :
    StageResult State Iterator Accumulator Failure → Option Failure
  | .yield _ _ _ => none
  | .halt _ _ => none
  | .raise error => some error

end StageResult

/-- The result of one action execution: the reached state plus an optional
returned inverse to be recorded in the caller's accumulator (nested
registration). -/
structure ActionResult (State : Type u) (Accumulator : Type v) where
  state : State
  inverse? : Option Accumulator

/-- One landing of a stored flight token: a successful landing binds the landed
state and the inverse it produced; a failed landing is a genuine landing
failure, never reclassified as success. -/
inductive LandingOutcome (State : Type u) (Accumulator : Type v) (Failure : Type w) where
  | landed (state : State) (inverse : Accumulator)
  | failed (failure : Failure)

namespace LandingOutcome

/-- The landed state of a successful landing; `none` for a landing failure. -/
def state? {State : Type u} {Accumulator : Type v} {Failure : Type w} :
    LandingOutcome State Accumulator Failure → Option State
  | .landed state _ => some state
  | .failed _ => none

end LandingOutcome

/-- External semantic interpretation for a component code. Each code family
carries its own universe so the profile instantiates over mixed-universe
carriers like `GlobalState`.  The frame relations are abstract here and are
instantiated non-vacuously in the fixtures: `observes` (reads respect the
owner's required/coeffect window), `writesWithinProvision` (writes stay in
the given provision envelope), `registryFrame` (foreign fibers and static
declarations unchanged — stage/landing bodies only), `domainFrame` (registry
keys unchanged — the accumulator may retire recorded children but never
allocates), `allocationFrame` (ledger and allocation history unchanged),
`accumulatorFrame` (the explicit owner/recorded-child cleanup frame).  Every
code family declares its own provision envelope via the `*Envelope` fields. -/
structure ComponentSemantics (Key : Type u) (State : Type u) (Value : Type v) (Action : Type w)
    (Iterator : Type x) (Accumulator : Type y) (Flight : Type z) (Failure : Type x) where
  action : Action → State → Option (ActionResult State Accumulator)
  stage : Iterator → State → Option (StageResult State Iterator Accumulator Failure)
  composeInverse : Accumulator → Accumulator → Accumulator
  identityAccumulator : Accumulator
  accumulator : Accumulator → State → Option State
  launch : State → Option Flight
  landing : Flight → State → Option (LandingOutcome State Accumulator Failure)
  failureBridge : Failure → State → Accumulator → Failure → Prop
  undo : State → Option State
  observes : State → State → Prop
  writesWithinProvision : Finset Key → State → State → Prop
  continuationStable : State → State → Prop
  registryFrame : State → State → Prop
  domainFrame : State → State → Prop
  allocationFrame : State → State → Prop
  rank : Iterator → Nat
  accumulatorFrame : Accumulator → State → State → Prop
  stageEnvelope : Iterator → Finset Key
  landingEnvelope : Flight → Finset Key
  accumulatorEnvelope : Accumulator → Finset Key
  actionEnvelope : Action → Finset Key
  action_writesWithinProvision : ∀ {code before result}, action code before = some result →
    writesWithinProvision (actionEnvelope code) before result.state
  action_frame : ∀ {code before result}, action code before = some result →
    observes before result.state
  action_registryFrame : ∀ {code before result}, action code before = some result →
    registryFrame before result.state
  action_allocationFrame : ∀ {code before result}, action code before = some result →
    allocationFrame before result.state
  inverse_law : ∀ {code before result}, action code before = some result →
    undo result.state = some before
  stage_frame : ∀ {code before result after}, stage code before = some result →
    result.state? = some after → observes before after
  stage_writesWithinProvision : ∀ {code before result after},
    stage code before = some result → result.state? = some after →
      writesWithinProvision (stageEnvelope code) before after
  stage_registryFrame : ∀ {code before result after}, stage code before = some result →
    result.state? = some after → registryFrame before after
  stage_allocationFrame : ∀ {code before result after}, stage code before = some result →
    result.state? = some after → allocationFrame before after
  stage_inverse : ∀ {code before result inverse after}, stage code before = some result →
    result.inverse? = some inverse → result.state? = some after →
      accumulator inverse after = some before
  relation_respect : ∀ {code left right left' right'}, observes left right →
    action code left = some left' → action code right = some right' →
      observes left'.state right'.state
  rank_law : ∀ {code before result next inverse after}, stage code before = some result →
    result = .yield after inverse next → rank next < rank code
  landing_stable : ∀ {token before state inverse}, landing token before =
      some (.landed state inverse) → continuationStable before state
  landing_frame : ∀ {token before outcome after}, landing token before = some outcome →
    outcome.state? = some after → observes before after
  landing_writesWithinProvision : ∀ {token before outcome after},
    landing token before = some outcome → outcome.state? = some after →
      writesWithinProvision (landingEnvelope token) before after
  landing_registryFrame : ∀ {token before outcome after},
    landing token before = some outcome → outcome.state? = some after →
      registryFrame before after
  landing_allocationFrame : ∀ {token before outcome after},
    landing token before = some outcome → outcome.state? = some after →
      allocationFrame before after
  failureBridge_law : ∀ {error before accPrefix failure failure'},
    failureBridge error before accPrefix failure → failureBridge error before accPrefix failure' →
      failure = failure'
  composeInverse_law : ∀ {a b before mid after}, accumulator b before = some mid →
    accumulator a mid = some after → accumulator (composeInverse a b) before = some after
  identityAccumulator_law : ∀ state, accumulator identityAccumulator state = some state
  accumulator_frame : ∀ {code before after}, accumulator code before = some after →
    accumulatorFrame code before after
  accumulator_writesWithinProvision : ∀ {code before after},
    accumulator code before = some after →
      writesWithinProvision (accumulatorEnvelope code) before after
  accumulator_domainFrame : ∀ {code before after}, accumulator code before = some after →
    domainFrame before after
  accumulator_allocationFrame : ∀ {code before after}, accumulator code before = some after →
    allocationFrame before after
  accumulator_observes : ∀ {code before after}, accumulator code before = some after →
    observes before after

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
