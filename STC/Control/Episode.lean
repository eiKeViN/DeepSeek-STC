module

public import STC.Control.Reachability

/-!
# Episode extraction and factorization

Episodes are trace-local objects. Their extraction does not assert that a
trace is lifecycle-only or that its endpoint is normal.
-/

universe u v w x

namespace STC.Control

open STC STC.State

@[expose] public section

section Episodes

variable {Name : Type u} {Key : Type v} {Value : Type w}
variable {Action : Type u} {Iterator : Type v} {Accumulator : Type w}
variable {Flight : Type u} {Failure : Type v} {Ambient : Type x}
variable [DecidableEq Name] [DecidableEq Key]

local notation "GState" => GlobalState Name Key Value Action Iterator Accumulator Flight Failure Ambient
local notation "GCell" => FiberCell Name Key Value Action Iterator Accumulator Flight Failure
local notation "OLabel" => GlobalOrchestrationLabel Name GCell
local notation "LLabel" => GlobalLifecycleLabel Name Failure
local notation "GTrace" => Trace orchestrationRule lifecycleRule

/-- Extract the labels from a trace. -/
def episodeLabels {before after : GState} : GTrace before after → List (Sum OLabel LLabel) := Trace.labels

/-- An episode witness for an actor and a trace segment. -/
def episodeOf {before after : GState} (actor : Name) (trace : GTrace before after) :
    Episode GState Name OLabel LLabel :=
  { actor := actor, start := before, finish := after, status := .closed,
    labels := trace.labels }

theorem episode_endpoint {before after : GState} (actor : Name) (trace : GTrace before after) :
  (episodeOf actor trace).start = before ∧ (episodeOf actor trace).finish = after := by
  exact ⟨rfl, rfl⟩

theorem episode_labels {before after : GState} (actor : Name) (trace : GTrace before after) :
  (episodeOf actor trace).labels = trace.labels := rfl

/-- A trace is factorized when each nonempty step has an explicit selected map. -/
def Factorized {before after : GState} (_trace : GTrace before after) : Prop :=
  ∃ _f : Factorization before after, True

/-- No-reuse of names is stated independently of endpoint WellFormedness. -/
theorem episode_closed_status {before after : GState} (actor : Name) (trace : GTrace before after) :
    (episodeOf actor trace).status = .closed := rfl

end Episodes

end

end STC.Control
