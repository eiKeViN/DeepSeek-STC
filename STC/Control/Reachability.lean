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

local notation "GState" =>
  GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient
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

local notation "IProfile" => InitialProfile (Name := Name) (Key := Key) (Value := Value)
  (Action := Action) (Iterator := Iterator) (Accumulator := Accumulator)
  (Flight := Flight) (Failure := Failure) (Ambient := Ambient)

/-- Reached state means an initial state followed by an actual typed trace. -/
def ReachedFrom (profile : IProfile) (before after : GState) : Prop :=
  profile.initial before ∧ profile.wellFormed before ∧ Nonempty (GTrace before after)

def Reachable (profile : IProfile) (state : GState) : Prop :=
  ∃ source, ReachedFrom profile source state

theorem reached_trace (profile : IProfile) {before after : GState}
    (h : ReachedFrom profile before after) : Nonempty (GTrace before after) := h.2.2

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
  replay : controlEdit (selectedMap before) = after
  edit_nonconstant : ∃ left right, left ≠ right ∧ selectedMap left ≠ selectedMap right

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
  ∃ fresh cell parent parentCell, label = .inl (.insert fresh cell) ∧
    cell.parent = some parent ∧ Finmap.lookup parent before.registry = some parentCell ∧
      orchestrationRule (.insert fresh cell) before after

/-- Activation provenance records either an initial commit certificate or a
trace-local successful finish. -/
inductive ActivationProvenance (profile : IProfile) (owner : Name) : GState → Prop
  | initial {state} : profile.activationCommit owner state →
      ActivationProvenance profile owner state
  | finished {before after : GState} :
      lifecycleRule (.finish owner) before after → ActivationProvenance profile owner after

/-- A partial bijection that can grow as fresh names are allocated. -/
structure GrowingBijection (Name : Type u) where
  forward : Name → Name → Prop
  leftUnique : ∀ {a b c}, forward a b → forward a c → b = c
  rightUnique : ∀ {a b c}, forward a c → forward b c → a = b

/-- Identity is the smallest total growing-bijection witness. -/
def GrowingBijection.identity (Name : Type u) : GrowingBijection Name where
  forward := Eq
  leftUnique := by
    intro a b c hab hac
    exact hab.symm.trans hac
  rightUnique := by
    intro a b c hac hbc
    exact hac.trans hbc.symm

/-- Optional parent names are compared through the growing bijection. -/
def RelatedOptionalName (bijection : GrowingBijection Name) : Option Name → Option Name → Prop
  | none, none => True
  | some left, some right => bijection.forward left right
  | _, _ => False

/-- Insert payloads retain all non-name data and rename both incarnation and parent;
committed provider-view names are compared through the same bijection. -/
def RelatedCell (bijection : GrowingBijection Name) (left right : GCell) : Prop :=
  bijection.forward left.incarnation right.incarnation ∧
    RelatedOptionalName bijection left.parent right.parent ∧
    left.birth = right.birth ∧ left.component = right.component ∧
    left.committed = right.committed ∧
    (∀ key, RelatedOptionalName bijection (Finmap.lookup key left.committedView)
      (Finmap.lookup key right.committedView)) ∧
    left.retired = right.retired ∧
    left.phase = right.phase ∧ left.payload = right.payload

/-- Two orchestration inputs retain their constructor, payload, parent, and renamed actor. -/
def RelatedOrchestrationInput (bijection : GrowingBijection Name) : OLabel → OLabel → Prop
  | .insert fresh left, .insert fresh' right =>
      bijection.forward fresh fresh' ∧ RelatedCell bijection left right
  | .retire left, .retire right => bijection.forward left right
  | .remove left, .remove right => bijection.forward left right
  | _, _ => False

/-- Discard lifecycle resolution details and retain the ordered orchestration inputs only. -/
def orchestrationInputs : List (Sum OLabel LLabel) → List OLabel
  | [] => []
  | .inl label :: rest => label :: orchestrationInputs rest
  | .inr _ :: rest => orchestrationInputs rest

def SameOrderedOrchestrationInputs {before after : GState}
    (left right : GTrace before after) : Prop :=
  ∃ bijection : GrowingBijection Name,
    List.Forall₂ (RelatedOrchestrationInput bijection)
      (orchestrationInputs left.labels) (orchestrationInputs right.labels)

/-- A stronger internal relation retaining resolved action/iterator/landing
witnesses. -/
def SameResolvedSemanticWitnesses {before after : GState}
    (left right : GTrace before after) : Prop :=
  left.labels = right.labels

theorem trace_append_reached (profile : IProfile) {a b c : GState}
    (h : ReachedFrom profile a b) (tail : GTrace b c) : ReachedFrom profile a c := by
  rcases h.2.2 with ⟨tr⟩
  exact ⟨h.1, h.2.1, Nonempty.intro (Trace.append tr tail)⟩

theorem trace_split {before after : GState} (trace : GTrace before after) (middle : GState)
    (left : GTrace before middle) (right : GTrace middle after)
    (h : Trace.append left right = trace) :
    trace.labels = left.labels ++ right.labels := by
  simpa [h] using Trace.append_labels left right

theorem sameResolved_implies_sameInputs {before after : GState} {left right : GTrace before after}
    (h : SameResolvedSemanticWitnesses left right) : SameOrderedOrchestrationInputs left right := by
  refine ⟨GrowingBijection.identity Name, ?_⟩
  rw [h]
  induction orchestrationInputs right.labels with
  | nil => exact .nil
  | cons label labels ih =>
      apply List.Forall₂.cons
      · cases label with
        | insert fresh cell =>
            refine ⟨rfl, rfl, ?_⟩
            refine ⟨?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
            · cases cell.parent <;> simp [RelatedOptionalName, GrowingBijection.identity]
            · intro key
              cases Finmap.lookup key cell.committedView <;>
                simp [RelatedOptionalName, GrowingBijection.identity]
        | retire owner => rfl
        | remove owner => rfl
      · exact ih

end Reachability

end

end STC.Control
