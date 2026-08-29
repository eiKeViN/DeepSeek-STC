module

public import STC.Control.Reachability

/-!
# Rule-derived structural facts

Structural facts are represented by explicit profiles and lifted by induction
over the authoritative trace.
-/

universe u v

namespace STC.Control

@[expose] public section

/-- Declared read/write footprints of one rule. -/
structure Footprint (Name : Type u) (Key : Type v) where
  readKeys : Finset Key
  writeKeys : Finset Key
  allocated : Option Name
  retired : Finset Name

/-- Structural preservation profile for an arbitrary labelled transition system. -/
structure StructuralLaws (State : Type u) (Label : Type v)
    (rule : Label → State → State → Prop) (wellFormed : State → Prop) where
  wellFormed_step : ∀ {label before after}, rule label before after →
    wellFormed before → wellFormed after
  frame : ∀ {label before after}, rule label before after → Prop
  observation : ∀ {label before after}, rule label before after → Prop

theorem oneStep_wellFormed {State : Type u} {Label : Type v}
    {rule : Label → State → State → Prop} {wellFormed : State → Prop}
    (laws : StructuralLaws State Label rule wellFormed)
    {label before after} (hstep : rule label before after) (hbefore : wellFormed before) :
    wellFormed after := laws.wellFormed_step hstep hbefore

/-- Same-label applicability and successor observation remain explicit. -/
structure SameLabelBisim (State : Type u) (Label : Type v)
    (rule : Label → State → State → Prop) (obs : State → State → Prop) where
  forward : ∀ {label : Label} {before after before' : State}, rule label before after →
    obs before before' → ∃ after' : State, rule label before' after' ∧ obs after after'
  backward : ∀ {label : Label} {before before' after' : State}, rule label before' after' →
    obs before before' → ∃ after : State, rule label before after ∧ obs after after'

end

end STC.Control
