module

public import STC.Control.Structural

/-!
# Lifecycle progress contracts

Progress is stated over a structurally defined readiness predicate and a
well-founded measure. Readiness is not defined as successor existence.
-/

universe u v

namespace STC.Control

@[expose] public section

structure ProgressMeasure (State : Type u) (Label : Type v)
    (step : Label → State → State → Prop) where
  rank : State → Nat
  decreases : ∀ {label before after}, step label before after → rank after < rank before
  ready : State → Prop
  ready_step : ∀ {label before after}, step label before after → ready before → ready after
  successor_or_quiescent : State → Prop

theorem progress_decreases {State : Type u} {Label : Type v}
    {step : Label → State → State → Prop}
    (profile : ProgressMeasure State Label step)
    {label before after} (h : step label before after) :
    profile.rank after < profile.rank before := profile.decreases h

theorem progress_ready_preserved {State : Type u} {Label : Type v}
    {step : Label → State → State → Prop}
    (profile : ProgressMeasure State Label step)
    {label before after} (h : step label before after) (ready : profile.ready before) :
    profile.ready after := profile.ready_step h ready

end

end STC.Control
