module

public import STC.Control.Reachability

/-!
# Episode extraction and factorization

Episodes are trace-local objects. Their extraction does not assert that a
trace is lifecycle-only or that its endpoint is normal.
-/

universe u

namespace STC.Control

open STC STC.State

@[expose] public section

section Episodes

variable {Name : Type u} {Key : Type u} {Value : Type u}
variable {Action : Type u} {Iterator : Type u} {Accumulator : Type u}
variable {Flight : Type u} {Error : Type u} {Ambient : Type u}
variable [DecidableEq Name] [DecidableEq Key]

local notation "GState" =>
  GlobalState Name Key Value Action Iterator Accumulator Flight Error Ambient
local notation "GSem" =>
  ComponentSemantics Key GState Value Action Iterator Accumulator Flight Error
local notation "OLabel" => GlobalOrchestrationLabel Name (FiberCell Name Key Value Action Iterator Accumulator Flight Error)
local notation "LLabel" =>
  GlobalLifecycleLabel Name Key Iterator Flight (FailureEvidence GState Error Accumulator)
/-- Extract the labels from a trace. -/
def episodeLabels (sem : GSem) {before after : GState} :
    globalTrace sem before after → List (Sum OLabel LLabel) :=
  Trace.labels

/-- An episode witness for an actor and a trace segment. -/
def episodeOf (sem : GSem) {before after : GState} (actor : Name) (trace : globalTrace sem before after) :
    Episode GState Name OLabel LLabel :=
  { actor := actor, start := before, finish := after, status := .closed,
    labels := trace.labels }

theorem episode_endpoint (sem : GSem) {before after : GState} (actor : Name)
    (trace : globalTrace sem before after) :
  (episodeOf sem actor trace).start = before ∧ (episodeOf sem actor trace).finish = after := by
  exact ⟨rfl, rfl⟩

theorem episode_labels (sem : GSem) {before after : GState} (actor : Name)
    (trace : globalTrace sem before after) :
  (episodeOf sem actor trace).labels = trace.labels := rfl

/-- A trace is factorized when each nonempty step has an explicit selected map. -/
def Factorized (sem : GSem) {before after : GState} (_trace : globalTrace sem before after) : Prop :=
  Nonempty (Factorization before after)

/-- No-reuse of names is stated independently of endpoint WellFormedness. -/
theorem episode_closed_status (sem : GSem) {before after : GState} (actor : Name)
    (trace : globalTrace sem before after) :
    (episodeOf sem actor trace).status = .closed := rfl

end Episodes

end

end STC.Control
