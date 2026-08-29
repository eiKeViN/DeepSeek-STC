module

public import STC.Control.Support
public import STC.Staging

/-!
# Support transport through Staging macros

The bridge consumes `MacroPath.trace` and the derived `RbOrch`/`RbLife`
relations.  It supplies conditional support-certificate transport without
turning the base view into an independent transition relation.
-/

universe u v w x y z

namespace STC.Staging

open STC STC.Control

@[expose] public section

section MacroSupport

variable {N : Type u} {K : Type v} [DecidableEq N] [DecidableEq K]

/-- A per-full-trace support contract for one Staging model. -/
structure MacroSupportContract
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type w}
    (model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel)
    (snapshot : ExtendedState → SupportSnapshot N K) : Prop where
  path_preserves : ∀ {labels before after},
    MacroPath model labels before after →
      HasCommittedSupport snapshot before → HasCommittedSupport snapshot after

/-- A profile-approved orchestration macro transports its support certificate. -/
theorem orchestration_macro_support
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type w}
    {model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel}
    {snapshot : ExtendedState → SupportSnapshot N K}
    (contract : MacroSupportContract model snapshot)
    {label : BaseOrchLabel} {before after : BaseState}
    (macroPath : RbOrch model label before after)
    (hbefore : HasCommittedSupport snapshot (model.embed before)) :
    HasCommittedSupport snapshot (model.embed after) := by
  rcases macroPath.2 with ⟨path⟩
  exact contract.path_preserves path hbefore

/-- A profile-approved lifecycle macro transports its support certificate. -/
theorem lifecycle_macro_support
    {BaseState ExtendedState BaseOrchLabel FullOrchLabel BaseLifeLabel FullLifeLabel : Type w}
    {model : StagingModel BaseState ExtendedState BaseOrchLabel FullOrchLabel
      BaseLifeLabel FullLifeLabel}
    {snapshot : ExtendedState → SupportSnapshot N K}
    (contract : MacroSupportContract model snapshot)
    {label : BaseLifeLabel} {before after : BaseState}
    (macroPath : RbLife model label before after)
    (hbefore : HasCommittedSupport snapshot (model.embed before)) :
    HasCommittedSupport snapshot (model.embed after) := by
  rcases macroPath.2 with ⟨path⟩
  exact contract.path_preserves path hbefore

/-- A permitted tagged stutter transports a certificate only via endpoint equality. -/
theorem stutter_support_transport
    {C : Type w} {snapshot : C → SupportSnapshot N K}
    {before after : C} (endpoint : before = after)
    (hbefore : HasCommittedSupport snapshot before) :
    HasCommittedSupport snapshot after := by
  simpa [endpoint] using hbefore

/-- Algebraic support-equals-active hook for later quiescence proofs. -/
theorem supportSet_eq_active
    (snapshot : SupportSnapshot N K) (order : SupportOrder snapshot)
    (active : Set N) (hfixed : SupportOperator snapshot active = active) :
    SupportSet snapshot = active :=
  supportSet_eq_of_fixed snapshot order hfixed

end MacroSupport

end

end STC.Staging
