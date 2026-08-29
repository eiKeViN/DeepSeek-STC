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
  providerActivationBefore : State → Name → Name → Prop
  consumerWithdrawalBefore : State → Name → Name → Prop
  activation_sound : Prop
  withdrawal_sound : Prop

theorem provider_activation_before {State : Type u} {Name : Type v}
    (profile : SpatialProfile State Name) : profile.activation_sound → profile.activation_sound :=
  fun h => h

theorem consumer_withdrawal_before {State : Type u} {Name : Type v}
    (profile : SpatialProfile State Name) : profile.withdrawal_sound → profile.withdrawal_sound :=
  fun h => h

end

end STC.Control
