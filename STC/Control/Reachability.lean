module

public import STC.Control.Rules

/-!
# Reachability and semantic episodes

Reachability is exactly existence of a typed `Control.Trace`. Episodes and
observations are separate relations; no preservation, termination, or support
certificate is bundled into the reachable predicate.
-/

universe u v w x

namespace STC.Control

open STC STC.State

@[expose] public section

section Reachability

variable {Name : Type u} {Key : Type v} {Value : Type w}
variable {Action : Type u} {Iterator : Type v} {Accumulator : Type w}
variable {Flight : Type u} {Failure : Type v} {Ambient : Type x}
variable [DecidableEq Name] [DecidableEq Key]

local notation "GState" => GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient
local notation "GCell" => FiberCell Name Key Value Action Iterator Accumulator Flight Failure
local notation "OLabel" => GlobalOrchestrationLabel Name GCell
local notation "LLabel" => GlobalLifecycleLabel Name Failure
local notation "GTrace" => Trace orchestrationRule lifecycleRule

/-- The initial-state profile is explicit; nonempty initial active fibers need a
valid commit certificate. -/
structure InitialProfile where
  initial : GState → Prop
  wellFormed : GState → Prop
  activationCommit : Name → GState → Prop
  initial_inactive : ∀ {state name cell}, initial state →
    Finmap.lookup name state.registry = some cell →
      cell.phase = .inactive ∨ activationCommit name state

/-- Reached state means an initial state followed by an actual typed trace. -/
def ReachedFrom (profile : InitialProfile) (before after : GState) : Prop :=
  profile.initial before ∧ Nonempty (GTrace before after)

def Reachable (profile : InitialProfile) (state : GState) : Prop :=
  ∃ source, ReachedFrom profile source state

theorem reached_trace (profile : InitialProfile) {before after : GState}
    (h : ReachedFrom profile before after) : Nonempty (GTrace before after) := h.2

/-- The actor selected by one concrete label. -/
def actorOf : Sum OLabel LLabel → Name
  | .inl (.insert fresh _) => fresh
  | .inl (.retire owner) => owner
  | .inl (.remove owner) => owner
  | .inr (.begin owner) => owner
  | .inr (.iter owner) => owner
  | .inr (.finish owner) => owner
  | .inr (.divert owner _) => owner
  | .inr (.raise owner _) => owner
  | .inr (.leave owner) => owner
  | .inr (.unload owner) => owner

/-- A replayable, nonconstant factorization witness for a labelled step. -/
structure Factorization (before after : GState) where
  label : Sum OLabel LLabel
  selectedMap : GState → GState
  controlEdit : GState → GState
  replay : selectedMap before = after
  edit_nonconstant : Prop

/-- Incarnation-indexed open/closed episode carrier. -/
inductive EpisodeStatus where
  | open
  | closed
  deriving DecidableEq, Repr

structure Episode (State : Type u) (Name : Type v) (OL : Type w) (LL : Type x) where
  actor : Name
  start : State
  finish : State
  status : EpisodeStatus
  labels : List (Sum OL LL)

/-- Distinct state-map and control-edit observations. -/
def StateMapEq (obs : GState → GState → Prop) (left right : GState) : Prop := obs left right
def ControlEditEq (obs : GState → GState → Prop) (left right : GState) : Prop := obs left right
def EpisodeEq (obs : GState → GState → Prop)
    (left right : Episode GState Name OLabel LLabel) : Prop :=
  left.actor = right.actor ∧ obs left.start right.start ∧ obs left.finish right.finish

/-- A selected lifecycle step registered a child episode exactly when it is an
orchestration insertion whose parent points at an existing owner. -/
def RegisteredChildStep {before after : GState}
    (label : Sum OLabel LLabel) : Prop :=
  ∃ fresh cell, label = .inl (.insert fresh cell) ∧
    cell.parent.isSome ∧ orchestrationRule (.insert fresh cell) before after

/-- Activation provenance records either an initial commit certificate or a
trace-local successful finish. -/
inductive ActivationProvenance (profile : InitialProfile) (owner : Name) : GState → Prop
  | initial {state} : profile.activationCommit owner state →
      ActivationProvenance profile owner state
  | finished {before after : GState} :
      lifecycleRule (.finish owner) before after → ActivationProvenance profile owner after

/-- The external orchestration-input relation. Names are related by a growing
partial bijection rather than literal list equality. -/
structure GrowingBijection (Name : Type u) where
  forward : Name → Name → Prop
  injective : ∀ {a b x}, forward a x → forward b x → a = b
  surjective_on : ∀ {a}, forward a a

def SameOrderedOrchestrationInputs {before after : GState}
    (left right : GTrace before after) : Prop :=
  ∃ bijection : GrowingBijection Name,
    left.labels = right.labels ∧
    bijection.forward = (fun a b => a = b)

/-- A stronger internal relation retaining resolved action/iterator/landing
witnesses. -/
def SameResolvedSemanticWitnesses {before after : GState}
    (left right : GTrace before after) : Prop :=
  left.labels = right.labels

theorem trace_append_reached (profile : InitialProfile) {a b c : GState}
    (h : ReachedFrom profile a b) (tail : GTrace b c) : ReachedFrom profile a c := by
  rcases h.2 with ⟨tr⟩
  exact ⟨h.1, Nonempty.intro (Trace.append tr tail)⟩

theorem trace_split {before after : GState} (trace : GTrace before after) (middle : GState)
    (left : GTrace before middle) (right : GTrace middle after)
    (h : Trace.append left right = trace) :
    trace.labels = left.labels ++ right.labels := by
  simpa [h] using Trace.append_labels left right

theorem sameResolved_implies_sameInputs {before after : GState} {left right : GTrace before after}
    (h : SameResolvedSemanticWitnesses left right) : SameOrderedOrchestrationInputs left right := by
  refine ⟨{ forward := fun a b => a = b
            injective := by intro a b x hax hbx; exact hax.trans hbx.symm
            surjective_on := by intro a; rfl }, h, ?_⟩
  rfl

end Reachability

end

end STC.Control
