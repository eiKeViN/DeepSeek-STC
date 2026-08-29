module

public import STC.Control.Structural
public import STC.State.Support.Closure

/-!
# Reachable support transport

This lane connects a supplied state projection to the existing positive support
closure, without placing a support certificate in `WellFormed`.
-/

universe u v

namespace STC.Control

open STC

variable {Name : Type v} [DecidableEq Name]

@[expose] public section

structure ReachableSupportProfile (State : Type u) (Name : Type v) [DecidableEq Name]
    (step : Name → State → State → Prop) where
  snapshot : State → SupportSnapshot Name Unit
  preserves : ∀ {label before after}, step label before after →
    SupportWF (snapshot before) → SupportWF (snapshot after)
  reachable : State → Prop

theorem support_wf_step {State : Type u} {Name : Type v} [DecidableEq Name]
    {step : Name → State → State → Prop}
    (profile : ReachableSupportProfile State Name step)
    {label before after} (hstep : step label before after)
    (hbefore : SupportWF (profile.snapshot before)) :
    SupportWF (profile.snapshot after) := profile.preserves hstep hbefore

end

end STC.Control
