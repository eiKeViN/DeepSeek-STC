module

public import STC.Alpha.Core
public import STC.Control.Reachability

/-!
# Global alpha transport contracts

Global state/name transport is parameterized by an explicit action and an
equivariance law; provision keys remain outside the permutation carrier.
-/

universe u v

namespace STC.Control

@[expose] public section

structure RuleAlphaProfile (Name : Type u) (State : Type v) (Label : Type v)
    (step : Label → State → State → Prop) where
  action : AlphaAction Name State
  renameLabel : Equiv.Perm Name → Label → Label
  equivariant : ∀ χ label before after, step label before after →
    step (renameLabel χ label) (action.act χ before) (action.act χ after)

theorem alpha_step {Name : Type u} {State Label : Type v}
    {step : Label → State → State → Prop}
    (profile : RuleAlphaProfile Name State Label step)
    (χ : Equiv.Perm Name) {label before after} (h : step label before after) :
    step (profile.renameLabel χ label) (profile.action.act χ before)
      (profile.action.act χ after) := profile.equivariant χ label before after h

end

end STC.Control
