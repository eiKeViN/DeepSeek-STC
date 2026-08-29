module

public import STC.Alpha.Transport
public import STC.Core.Iterator
public import STC.Foundation.Result

/-!
# Control relations and labelled traces

The control layer keeps externally chosen orchestration separate from internally
enabled lifecycle transitions.  Its finite trace carrier stores the relation
witness and preserves labels and endpoints for staging and later metatheory.

## Main declarations

* `ControlState`, `InFlight`, and `LandingWitness`;
* `OrchestrationLabel`, `LifecycleLabel`, `ControlModel`, and `Step`;
* `Trace`, `TracePolicy`, and lifecycle-suffix predicates;
* `AsyncPolicy` and `raiseLabel`.
-/

universe u v w x y

namespace STC.Control

@[expose] public section

section Carriers

inductive ControlMode where
  | inactive
  | reloading
  | active
  | unloading
  deriving DecidableEq, Repr

inductive LandingChoice where
  | abort
  | land
  deriving DecidableEq, Repr

/-- A future token is tied to the state predicate that makes landing admissible. -/
structure LandingWitness (S : Type u) (F : Type v) where
  future : F
  admissible : S → Prop

/-- The committed snapshot and successful-prefix undo for one in-flight operation. -/
structure InFlight (I S Q V F A : Type u) where
  owner : I
  launch : S
  committed : V
  remaining : Q
  prefixUndo : A
  landingWitness : LandingWitness S F

/-- Control state with explicit mode, in-flight boundary, and optional outcome. -/
structure ControlState (S M I Q V F E A : Type u) where
  raw : S
  traceMeta : M
  mode : ControlMode
  inFlight : Option (InFlight I S Q V F A)
  outcome : Option E

end Carriers

section Labels

inductive OrchestrationLabel (I : Type u) (P : Type v) where
  | insert (fresh : I) (payload : P)
  | retire (owner : I)
  | remove (owner : I)
    deriving Repr

inductive LifecycleLabel (I : Type u) (Q : Type v) (V : Type w)
    (S : Type x) (E : Type y) where
  | begin (owner : I) (target : V)
  | iter (owner : I) (next : Q)
  | finish (owner : I)
  | divert (owner : I) (choice : LandingChoice)
  | raise (owner : I) (failure : Failure S E)
  | leave (owner : I)
  | unload (owner : I)

/-- The two relation classes are packaged without introducing a scheduler. -/
structure ControlModel (OL : Type u) (LL : Type v) (C : Type w) where
  orchestration : OL → C → C → Prop
  lifecycle : LL → C → C → Prop

/-- A typed step retains its class, label, endpoints, and local relation premise. -/
inductive Step {OL : Type u} {LL : Type v} {C : Type w}
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop) : C → C → Type (max u v w) where
  | orchestration {before after : C} (label : OL)
      (premise : orchestration label before after) :
      Step orchestration lifecycle before after
  | lifecycle {before after : C} (label : LL)
      (premise : lifecycle label before after) :
      Step orchestration lifecycle before after

namespace Step

def label {OL : Type u} {LL : Type v} {C : Type w}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before after : C} :
    Step orchestration lifecycle before after → Sum OL LL
  | .orchestration label _ => .inl label
  | .lifecycle label _ => .inr label

def isLifecycle {OL : Type u} {LL : Type v} {C : Type w}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before after : C} :
    Step orchestration lifecycle before after → Bool
  | .orchestration _ _ => false
  | .lifecycle _ _ => true

end Step

end Labels

section Traces

inductive Trace {OL : Type u} {LL : Type v} {C : Type w}
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop) : C → C → Type (max u v w) where
  | nil {state : C} : Trace orchestration lifecycle state state
  | cons {before middle after : C}
      (head : Step orchestration lifecycle before middle)
      (tail : Trace orchestration lifecycle middle after) :
      Trace orchestration lifecycle before after

namespace Trace

def labels {OL : Type u} {LL : Type v} {C : Type w}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before after : C} :
    Trace orchestration lifecycle before after → List (Sum OL LL)
  | .nil => []
  | .cons head tail => Step.label head :: labels tail

def length {OL : Type u} {LL : Type v} {C : Type w}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before after : C} : Trace orchestration lifecycle before after → Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1

def onlyLifecycle {OL : Type u} {LL : Type v} {C : Type w}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before after : C} :
    Trace orchestration lifecycle before after → Prop
  | .nil => True
  | .cons (.orchestration _ _) _ => False
  | .cons (.lifecycle _ _) tail => onlyLifecycle tail

def append {OL : Type u} {LL : Type v} {C : Type w}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before middle after : C}
    (left : Trace orchestration lifecycle before middle)
    (right : Trace orchestration lifecycle middle after) :
    Trace orchestration lifecycle before after :=
  match left with
  | .nil => right
  | .cons head tail => .cons head (append tail right)

theorem append_labels {OL : Type u} {LL : Type v} {C : Type w}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before middle after : C}
    (left : Trace orchestration lifecycle before middle)
    (right : Trace orchestration lifecycle middle after) :
    (append left right).labels = left.labels ++ right.labels := by
  induction left with
  | nil => simp [append, labels]
  | @cons before middle mid head tail ih =>
      simp [append, labels, ih]

theorem length_append {OL : Type u} {LL : Type v} {C : Type w}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before middle after : C}
    (left : Trace orchestration lifecycle before middle)
    (right : Trace orchestration lifecycle middle after) :
    (append left right).length = left.length + right.length := by
  induction left with
  | nil => simp [append, length]
  | @cons before middle mid head tail ih =>
      simp [append, length, ih, Nat.add_assoc, Nat.add_comm]

end Trace

def HasLifecycleSuccessor {LL : Type u} {C : Type v}
    (lifecycle : LL → C → C → Prop) (state : C) : Prop :=
  ∃ label next, lifecycle label state next

def MaximalLifecycleSuffix {OL : Type u} {LL : Type v} {C : Type w}
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop)
    {before after : C}
    (trace : Trace orchestration lifecycle before after) : Prop :=
  trace.onlyLifecycle ∧ ¬ HasLifecycleSuccessor lifecycle after

structure TracePolicy (OL : Type u) (LL : Type v) (C : Type w) (M : Type x)
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop) where
  initial : M → Prop
  labelOk : List (Sum OL LL) → Bool
  stepOk : ∀ {before after : C}, M →
    Step orchestration lifecycle before after → Prop

def Trace.stepsOk {OL : Type u} {LL : Type v} {C : Type w} {M : Type x}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    (policy : TracePolicy OL LL C M orchestration lifecycle)
    (metadata : M) {before after : C} :
    Trace orchestration lifecycle before after → Prop
  | .nil => True
  | .cons head tail =>
      policy.stepOk metadata head ∧ stepsOk policy metadata tail

def Trace.admissible {OL : Type u} {LL : Type v} {C : Type w} {M : Type x}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    (policy : TracePolicy OL LL C M orchestration lifecycle)
    (metadata : M) {before after : C}
    (trace : Trace orchestration lifecycle before after) : Prop :=
  policy.initial metadata ∧ policy.labelOk trace.labels = true ∧
    trace.stepsOk policy metadata

def lifecycleOnlyPolicy (OL : Type u) (LL : Type v) (C : Type w) (M : Type x)
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop) :
    TracePolicy OL LL C M orchestration lifecycle where
  initial := fun _ => True
  labelOk := fun labels =>
    let rec go : List (Sum OL LL) → Bool
      | [] => true
      | .inl _ :: _ => false
      | .inr _ :: rest => go rest
    go labels
  stepOk := fun _ _ => True

theorem orchestration_not_onlyLifecycle
    {OL : Type u} {LL : Type v} {C : Type w}
    {orchestration : OL → C → C → Prop}
    {lifecycle : LL → C → C → Prop}
    {before middle after : C} (label : OL)
    (premise : orchestration label before middle)
    (tail : Trace orchestration lifecycle middle after) :
    ¬ (Trace.cons (.orchestration label premise) tail).onlyLifecycle := by
  simp [Trace.onlyLifecycle]

end Traces

section AsyncFailure

structure AsyncPolicy (F : Type u) (C : Type v) where
  atBoundary : F → C → Prop
  landingWitness : F → C → Prop
  allowed : F → C → LandingChoice → Prop
  mustLand : ∀ flight state, allowed flight state .land
  landSound : ∀ flight state, allowed flight state .land → landingWitness flight state
  abortGuard : ∀ flight state, allowed flight state .abort → atBoundary flight state

def landingAllowed {F : Type u} {C : Type v} (policy : AsyncPolicy F C)
    (flight : F) (state : C) (choice : LandingChoice) : Prop :=
  policy.allowed flight state choice

theorem landingAllowed_has_witness {F : Type u} {C : Type v}
    (policy : AsyncPolicy F C) (flight : F) (state : C)
    (h : landingAllowed policy flight state .land) :
    policy.landingWitness flight state :=
  policy.landSound flight state h

def raiseLabel {I S E Q V : Type u} (owner : I) :
    ExecResult S E → Option (LifecycleLabel I Q V S E)
  | .success _ => none
  | .failure failure => some (.raise owner failure)

theorem raiseLabel_failure_preserves {I S E Q V : Type u}
    (owner : I) (failure : Failure S E) :
    raiseLabel (Q := Q) (V := V) owner (.failure failure : ExecResult S E) =
      some (.raise owner failure) := rfl

theorem raiseLabel_success_absent {I S E Q V : Type u}
    (owner : I) (result : EffectResult S) :
    raiseLabel (Q := Q) (V := V) owner (.success result : ExecResult S E) = none := rfl

end AsyncFailure

end

end STC.Control
