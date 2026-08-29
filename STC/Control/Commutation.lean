module

public import STC.Control.Alpha

/-!
# Adjacent transposition contracts

The diamond theorem keeps disjoint footprints, same-witness replay, continuation
stability, and compatible control edits visible as separate premises.
-/

universe u v

namespace STC.Control

@[expose] public section

structure DiamondProfile (State : Type u) (Label : Type v)
    (step : Label → State → State → Prop) where
  disjoint : Label → Label → Prop
  sameWitness : State → State → Prop
  continuationStable : State → State → Prop
  compatibleEdit : State → State → Prop
  diamond : ∀ {a b c : State} {l₁ l₂ : Label},
    step l₁ a b → step l₂ b c → disjoint l₁ l₂ →
      ∃ d, step l₂ a d ∧ step l₁ d c

theorem adjacent_swap {State : Type u} {Label : Type v}
    {step : Label → State → State → Prop}
    (profile : DiamondProfile State Label step)
    {a b c : State} {l₁ l₂ : Label}
    (h₁ : step l₁ a b) (h₂ : step l₂ b c) (hdisjoint : profile.disjoint l₁ l₂) :
    ∃ d, step l₂ a d ∧ step l₁ d c := profile.diamond h₁ h₂ hdisjoint

end

end STC.Control
