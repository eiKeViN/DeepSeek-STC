module

public import STC.State.Component
public import STC.Alpha.Trace

/-!
# Positive fiber cells

Fiber cells retain incarnation identity, immutable birth order, declarations,
local committed data, lifecycle phase, and coded payloads. No field is indexed
by the containing raw state.
-/

universe u v w

namespace STC.State

@[expose] public section

section Fiber

variable {Name : Type u} {Key : Type v} {Value : Type w}
variable {Action : Type u} {Iterator : Type v} {Accumulator : Type w}
variable {Flight : Type u} {Failure : Type v}

inductive LifecyclePhase where
  | inactive
  | reloading
  | active
  | unloading
  | failed
  deriving DecidableEq, Repr

/-- Positive local data committed by a fiber. -/
structure CommittedData (Key : Type u) (Value : Type v) where
  entries : Finmap (fun _ : Key => Value)

/-- A data-only lifecycle payload. -/
structure FiberPayload (Iterator : Type u) (Accumulator : Type v)
    (Flight : Type w) (Failure : Type u) where
  iteratorCode : Iterator
  accumulatorCode : Accumulator
  flightCode : Option Flight
  failureData : Option Failure

/-- One incarnation in the global registry. -/
structure FiberCell (Name : Type u) (Key : Type v) (Value : Type w)
    (Action : Type u) (Iterator : Type v) (Accumulator : Type w)
    (Flight : Type u) (Failure : Type v) where
  incarnation : Name
  parent : Option Name
  birth : Nat
  component : Component Key Value Action Iterator Accumulator Flight Failure
  committed : CommittedData Key Value
  retired : Bool
  phase : LifecyclePhase
  payload : FiberPayload Iterator Accumulator Flight Failure

/-- Initial fibers are inactive unless an explicit commit certificate is supplied. -/
def InitiallyInactive (fiber : FiberCell Name Key Value Action Iterator Accumulator Flight Failure) : Prop :=
  fiber.phase = .inactive

def initiallyInactive_decidable
    (fiber : FiberCell Name Key Value Action Iterator Accumulator Flight Failure) :
    Decidable (InitiallyInactive fiber) := by
  unfold InitiallyInactive
  infer_instance

end Fiber

end

end STC.State
