module

public import STC.Control.Progress

/-!
# Progress-lane evidence
-/

namespace STC.Examples.GlobalProgress

open STC STC.Control

@[expose] public section

def profile : ProgressMeasure Nat Nat (fun _ before after => after < before) where
  rank := fun n => n
  decreases := by intro label before after h; exact h
  ready := fun _ => True
  ready_step := by intro label before after h hr; trivial
  quiescent := fun state => state = 0
  successor_or_quiescent := by
    intro state ready
    cases state with
    | zero => exact Or.inr rfl
    | succ predecessor => exact Or.inl ⟨0, predecessor, Nat.lt_succ_self predecessor⟩

end

end STC.Examples.GlobalProgress
