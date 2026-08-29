module

public import STC.Control.Support.Reachable
public import STC.Staging.Support

/-!
# Support at quiescence

The active-set fixed point is derived only after semantic total-provision and
quiescence premises are supplied.
-/

universe u v

namespace STC.Control

open STC

variable {Name : Type v} [DecidableEq Name]

@[expose] public section

structure QuiescenceSupportProfile (State : Type u) (Name : Type v) [DecidableEq Name]
    (active : State → Set Name) where
  snapshot : State → SupportSnapshot Name Unit
  quiescent : State → Prop
  nonfailed : State → Prop
  totalProvision : State → Prop
  supportOrder : ∀ state, SupportOrder (snapshot state)

theorem support_at_quiescence {State : Type u} {Name : Type v}
    [DecidableEq Name]
    {active : State → Set Name}
    (profile : QuiescenceSupportProfile State Name active)
    (state : State) (_hq : profile.quiescent state)
    (_hn : profile.nonfailed state) (_ht : profile.totalProvision state)
    (hfixed : SupportOperator (profile.snapshot state) (active state) = active state) :
    SupportSet (profile.snapshot state) = active state := by
  exact supportSet_eq_of_fixed (profile.snapshot state) (profile.supportOrder state) hfixed

end

end STC.Control
