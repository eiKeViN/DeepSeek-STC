module

public import STC.Control.Structural

/-!
# Single-realm spatial ordering

Provider-before-consumer and consumer-before-provider withdrawal are explicit
relations. No scoped resolver is used here.
-/

universe u v

namespace STC.Control

@[expose] public section

structure SpatialProfile (State : Type u) (Name : Type v) where
  providerDependency : State → Name → Name → Prop
  withdrawalDependency : State → Name → Name → Prop
  providerActivationBefore : State → Name → Name → Prop
  consumerWithdrawalBefore : State → Name → Name → Prop
  activation_sound : ∀ {state provider consumer},
    providerDependency state provider consumer →
      providerActivationBefore state provider consumer
  withdrawal_sound : ∀ {state provider consumer},
    withdrawalDependency state provider consumer →
      consumerWithdrawalBefore state consumer provider

theorem provider_activation_before {State : Type u} {Name : Type v}
    (profile : SpatialProfile State Name) {state provider consumer}
    (h : profile.providerDependency state provider consumer) :
    profile.providerActivationBefore state provider consumer :=
  profile.activation_sound h

theorem consumer_withdrawal_before {State : Type u} {Name : Type v}
    (profile : SpatialProfile State Name) {state provider consumer}
    (h : profile.withdrawalDependency state provider consumer) :
    profile.consumerWithdrawalBefore state consumer provider :=
  profile.withdrawal_sound h

end

end STC.Control
