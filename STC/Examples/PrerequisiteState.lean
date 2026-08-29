module

public import STC.Foundation.Relation.Transport
public import STC.State.Observation.Lift
public import STC.State.Positive

/-!
# Positive state prerequisite evidence
-/

namespace STC.Examples.PrerequisiteState

open STC STC.State

@[expose] public section

def cell : PositiveCell Nat Nat Bool := { key := 0, data := 7, code := true }

theorem cell_payload : cell.key = 0 ∧ cell.data = 7 ∧ cell.code = true := by
  exact ⟨rfl, rfl, rfl⟩

theorem identity_map_transport : RelMap (equality Nat) (equality Nat) id := relMap_id _

end

end STC.Examples.PrerequisiteState
