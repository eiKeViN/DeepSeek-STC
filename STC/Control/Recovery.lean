module

public import STC.Control.Episode
public import STC.Core.Partial.Recovery

/-!
# Lifecycle recovery contracts

Recovery theorems consume explicit inverse, continuation, landing, and cleanup
profiles. The profiles are not inferred from a finite trace.
-/

universe u v

namespace STC.Control

@[expose] public section

structure RecoveryProfile (State : Type u) (Label : Type v)
    (step : Label → State → State → Prop) where
  inverse : State → State → Prop
  continuationStable : State → State → Prop
  landingCoherent : State → State → Prop
  cleanup : State → State → Prop
  inverse_step : ∀ {label before after}, step label before after → inverse after before

theorem recovery_profile_inverse {State : Type u} {Label : Type v}
    {step : Label → State → State → Prop}
    (profile : RecoveryProfile State Label step) {label before after}
    (h : step label before after) : profile.inverse after before :=
  profile.inverse_step h

/-- The strong "as if never begun" result requires no registered-child steps. -/
structure NoRegisteredChildren (State : Type u) (Label : Type v)
    (step : Label → State → State → Prop) where
  registeredChild : Label → State → State → Prop
  absent : ∀ {label before after}, step label before after →
    ¬ registeredChild label before after

def RecoverableEpisode (State : Type u) (Label : Type v)
    (step : Label → State → State → Prop) (profile : RecoveryProfile State Label step)
    (before after : State) : Prop :=
  profile.inverse before after ∧ profile.continuationStable before after ∧
    profile.landingCoherent before after ∧ profile.cleanup before after

theorem recoverableEpisode_symm {State : Type u} {Label : Type v}
    {step : Label → State → State → Prop}
    (profile : RecoveryProfile State Label step) {before after : State}
    (h : RecoverableEpisode State Label step profile before after) :
    profile.inverse before after := h.1

end

end STC.Control
