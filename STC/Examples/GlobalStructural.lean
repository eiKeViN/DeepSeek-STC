module

public import STC.Control.Preservation
public import STC.Examples.GlobalRules

/-!
# Structural-lane evidence
-/

namespace STC.Examples.GlobalStructural

open STC STC.Control STC.State

@[expose] public section

def entry : Table1Entry := table1For "finish" "lifecycle"

theorem entry_case : entry.paperCase = "lifecycle" := rfl

/-! ### P13 semantic-freeze blockers -/

abbrev Cell := GlobalRules.Cell
abbrev State := GlobalRules.State

/-- The concrete parent-closure component required by the P13 WellFormed target. -/
def ParentClosed (state : State) : Prop :=
  ∀ owner cell parent, Finmap.lookup owner state.registry = some cell →
    cell.parent = some parent → parent ∈ state.registry.keys

def orphanCell : Cell := { GlobalRules.cell0 with incarnation := 1, parent := some 9, birth := 1 }

def orphanState : State := insertState GlobalRules.state0 1 orphanCell

theorem empty_parentClosed : ParentClosed GlobalRules.state0 := by
  intro owner cell parent h
  simp [GlobalRules.state0] at h

theorem orphan_insert_rule :
    orchestrationRule (.insert 1 orphanCell) GlobalRules.state0 orphanState := by
  simp [orchestrationRule, orphanState, GlobalRules.state0, insertState]

/-- The authoritative insert guard permits a fresh cell whose parent is absent. -/
theorem orphanState_not_parentClosed : ¬ ParentClosed orphanState := by
  intro h
  have hp := h 1 orphanCell 9 (by simp [orphanState, GlobalRules.state0, insertState]) rfl
  rw [Finmap.mem_keys, Finmap.mem_iff] at hp
  rcases hp with ⟨cell, hcell⟩
  have hnone : Finmap.lookup 9 (Finmap.insert 1 orphanCell (∅ : Finmap (fun _ : Nat => Cell))) =
      none := by
    rw [Finmap.lookup_insert_of_ne]
    · rfl
    · omega
  change Finmap.lookup 9 (Finmap.insert 1 orphanCell
    (∅ : Finmap (fun _ : Nat => Cell))) = some cell at hcell
  rw [hnone] at hcell
  cases hcell

/-- Consequently parent-closure preservation cannot be derived from the current rule guard. -/
theorem no_parentClosed_orchestration_preservation :
    ¬ (∀ label before after, orchestrationRule label before after →
      ParentClosed before → ParentClosed after) := by
  intro h
  exact orphanState_not_parentClosed
    (h (.insert 1 orphanCell) GlobalRules.state0 orphanState orphan_insert_rule
      empty_parentClosed)

/-- The current iterator rule has an inhabited lifecycle self-loop. -/
theorem iterator_self_loop :
    lifecycleRule (.iter 0) GlobalRules.stateReloading GlobalRules.stateReloading := by
  simpa [GlobalRules.stateReloading, GlobalRules.state1, GlobalRules.state0,
    phaseState, editCell, insertState, updateFiber] using GlobalRules.iter_rule

/-- No natural-number measure can strictly decrease on every current lifecycle step. -/
theorem no_strict_lifecycle_measure :
    ¬ ∃ rank : State → Nat, ∀ label before after,
      lifecycleRule label before after → rank after < rank before := by
  rintro ⟨rank, h⟩
  exact (Nat.lt_irrefl _)
    (h (.iter 0) GlobalRules.stateReloading GlobalRules.stateReloading iterator_self_loop)

end

end STC.Examples.GlobalStructural
