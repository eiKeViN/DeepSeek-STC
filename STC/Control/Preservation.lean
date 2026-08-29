module

public import STC.Control.Structural

/-!
# Preservation joins

Static, lifecycle, control-edit, and name preservation are separate contract
fields and can be consumed independently by later lanes.
-/

universe u v

namespace STC.Control

@[expose] public section

structure PreservationProfile (State : Type u) (Label : Type v)
    (rule : Label → State → State → Prop) where
  static : State → State → Prop
  lifecycle : State → State → Prop
  controlEdit : State → State → Prop
  names : State → State → Prop
  step_static : ∀ {label before after}, rule label before after → static before after
  step_lifecycle : ∀ {label before after}, rule label before after → lifecycle before after

theorem step_preserves_static {State : Type u} {Label : Type v}
    {rule : Label → State → State → Prop}
    (profile : PreservationProfile State Label rule)
    {label before after} (h : rule label before after) :
    profile.static before after := profile.step_static h

/-- The machine-derived Table1 record is evidence data, not an axiom. -/
structure Table1Entry where
  constructorName : String
  paperCase : String
  footprintRead : String
  footprintWrite : String
  staticLaw : String

def table1For (constructorName paperCase : String) : Table1Entry :=
  { constructorName := constructorName, paperCase := paperCase,
    footprintRead := "explicit", footprintWrite := "explicit", staticLaw := "profile" }

end

end STC.Control
