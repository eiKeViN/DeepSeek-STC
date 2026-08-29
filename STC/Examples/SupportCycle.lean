module

public import Mathlib.Tactic
public import STC.State.Support.Closure

/-!
# Support-cycle negative evidence

This is a finite semantic support projection with an explicit three-edge cycle.
It is recorded as a negative profile and is not presented as a reachable rule
trace until the concrete guarded rules establish that fact.
-/

namespace STC.Examples.SupportCycle

open STC

@[expose] public section

def cycleSnapshot : SupportSnapshot (Fin 3) Unit where
  dom := {0, 1, 2}
  retired := fun _ => false
  parent := fun n => if n = 1 then some 0 else if n = 2 then some 1 else some 2
  requires := fun n => if n = 2 then {0} else ∅
  provides := fun _ => ∅
  birth := fun n => n.val

theorem cycle_edges :
    SupportRel cycleSnapshot 0 1 ∧ ParentEdge cycleSnapshot 1 2 ∧
      ParentEdge cycleSnapshot 2 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Or.inr (by rfl)
  · rfl
  · rfl

theorem cycle_not_supportWF : ¬ SupportWF cycleSnapshot := by
  rintro ⟨order⟩
  have h01 := order.edge_lt (a := (0 : Fin 3)) (b := (1 : Fin 3)) (by simp [cycleSnapshot])
    (by simp [cycleSnapshot]) (Or.inr (by rfl))
  have h12 := order.edge_lt (a := (1 : Fin 3)) (b := (2 : Fin 3)) (by simp [cycleSnapshot])
    (by simp [cycleSnapshot]) (Or.inr (by rfl))
  have h20 := order.edge_lt (a := (2 : Fin 3)) (b := (0 : Fin 3)) (by simp [cycleSnapshot])
    (by simp [cycleSnapshot]) (Or.inr (by rfl))
  omega

end

end STC.Examples.SupportCycle
