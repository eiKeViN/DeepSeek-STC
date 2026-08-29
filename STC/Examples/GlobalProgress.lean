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
  successor_or_quiescent := fun _ => True

end

end STC.Examples.GlobalProgress
