module

public import Mathlib.Data.Finmap
public import STC.Foundation.Relation
public import STC.State.CoeffectStore

/-!
# Positive state and context carriers

The generic state shell stores only data and codes.  It contains no state-indexed
function, proposition, iterator, or in-flight closure.
-/

universe u v w

namespace STC.State

@[expose] public section

section Positive

variable {K : Type u} {D : Type v} {Code : Type w}

/-- A registry cell with data-only payload and behavior code. -/
structure PositiveCell (K : Type u) (D : Type v) (Code : Type w) where
  key : K
  data : D
  code : Code

/-- A finite positive registry of cells. -/
abbrev PositiveRegistry (K : Type u) (D : Type v) (Code : Type w) :=
  Finmap (fun _ : K => PositiveCell K D Code)

/-- An ambient context and its positive registry. -/
structure PositiveContext (Ambient : Type u) (K : Type v) (D : Type w) (Code : Type u) where
  ambient : Ambient
  registry : PositiveRegistry K D Code

/-- The registry has no negative recursive occurrence. -/
def CellDataOnly (_cell : PositiveCell K D Code) : Prop :=
  True

theorem positiveRegistry_empty (K : Type u) (D : Type v) (Code : Type w) :
    (∅ : PositiveRegistry K D Code).keys = ∅ := by
  rfl

end Positive

end

end STC.State
