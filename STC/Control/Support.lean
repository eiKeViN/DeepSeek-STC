module

public import STC.Control
public import STC.State.Support.Closure

/-!
# Support certificates along Control traces

The bridge projects each control state to a committed support snapshot and
keeps orchestration and lifecycle preservation as separate obligations.
-/

universe u v w x y

namespace STC.Control

open STC

@[expose] public section

section SupportBridge

variable {N : Type u} {K : Type v} {OL : Type x} {LL : Type y} {C : Type w}
  [DecidableEq N] [DecidableEq K]

/-- A state carries a committed support certificate for its projected snapshot. -/
def HasCommittedSupport (snapshot : C → SupportSnapshot N K) (state : C) : Prop :=
  Nonempty (CommittedSnapshot (snapshot state))

/-- Separate support-preservation obligations for the two Control relation classes. -/
structure SupportTraceContract
    (snapshot : C → SupportSnapshot N K)
    (orchestration : OL → C → C → Prop)
    (lifecycle : LL → C → C → Prop) : Prop where
  orchestration_preserves : ∀ {label before after},
    orchestration label before after →
      HasCommittedSupport snapshot before → HasCommittedSupport snapshot after
  lifecycle_preserves : ∀ {label before after},
    lifecycle label before after →
      HasCommittedSupport snapshot before → HasCommittedSupport snapshot after

theorem trace_support_preserves
    {orchestration : OL → C → C → Prop} {lifecycle : LL → C → C → Prop}
    {snapshot : C → SupportSnapshot N K}
    (contract : SupportTraceContract snapshot orchestration lifecycle)
    {before after : C} (trace : Trace orchestration lifecycle before after)
    (hinitial : HasCommittedSupport snapshot before) :
    HasCommittedSupport snapshot after := by
  induction trace with
  | nil => exact hinitial
  | @cons before middle after head tail ih =>
      apply ih
      cases head with
      | orchestration label premise =>
          exact contract.orchestration_preserves premise hinitial
      | lifecycle label premise =>
          exact contract.lifecycle_preserves premise hinitial

/-- Every endpoint of a certified trace exposes a support order. -/
theorem trace_endpoint_supportWF
    {orchestration : OL → C → C → Prop} {lifecycle : LL → C → C → Prop}
    {snapshot : C → SupportSnapshot N K}
    (contract : SupportTraceContract snapshot orchestration lifecycle)
    {before after : C} (trace : Trace orchestration lifecycle before after)
    (hinitial : HasCommittedSupport snapshot before) :
    SupportWF (snapshot after) := by
  rcases trace_support_preserves contract trace hinitial with ⟨certificate⟩
  exact ⟨certificate.order⟩

/-- The endpoint order yields well-founded dependency-first induction. -/
theorem trace_endpoint_supportDep_wellFounded
    {orchestration : OL → C → C → Prop} {lifecycle : LL → C → C → Prop}
    {snapshot : C → SupportSnapshot N K}
    (contract : SupportTraceContract snapshot orchestration lifecycle)
    {before after : C} (trace : Trace orchestration lifecycle before after)
    (hinitial : HasCommittedSupport snapshot before) :
    ∃ _order : SupportOrder (snapshot after),
      WellFounded (fun (x y : {n // n ∈ (snapshot after).dom}) =>
        SupportDep (snapshot after) y.1 x.1) := by
  rcases trace_support_preserves contract trace hinitial with ⟨certificate⟩
  exact ⟨certificate.order,
    supportDep_wellFounded (snapshot after) certificate.order⟩

end SupportBridge

end

end STC.Control
