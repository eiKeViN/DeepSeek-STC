module

public import Mathlib.Tactic
public import STC.State.Support

/-!
# Support examples

Finite positive and negative profiles for the support core.  These are executable
evidence only; graph witnesses are not presented as lifecycle traces.
-/

namespace STC

@[expose] public section

private def demo : SupportSnapshot (Fin 3) (Fin 2) where
  dom := {0, 1, 2}
  retired := fun _ => false
  parent := fun n => if n = 0 then none else some ⟨n.val - 1, by omega⟩
  requires := fun n => if n = 2 then {0} else ∅
  provides := fun n => if n = 0 then {0} else ∅
  birth := fun n => n.val

private def demoOrder : SupportOrder demo where
  rank := fun n => n.val
  edge_lt := by
    intro a b ha hb h
    fin_cases a <;> fin_cases b <;>
      simp [SupportRel, Precedes, ParentEdge, demo] at h ⊢

example : SupportWF demo :=
  ⟨demoOrder⟩

example : WellFounded (fun (x y : {n // n ∈ demo.dom}) =>
    SupportDep demo y.1 x.1) :=
  supportDep_wellFounded demo demoOrder

example : SupportOperator demo (SupportSet demo) = SupportSet demo :=
  supportSet_fixed demo

private def cycle : SupportSnapshot (Fin 3) (Fin 2) where
  dom := {0, 1, 2}
  retired := fun _ => false
  parent := fun n => if n = 0 then none else if n = 1 then some 0 else some 1
  requires := fun n => if n = 0 then {0} else ∅
  provides := fun n => if n = 2 then {0} else ∅
  birth := fun n => n.val

example :
    SupportRel cycle (2 : Fin 3) 0 ∧
      SupportRel cycle 0 1 ∧ SupportRel cycle 1 2 := by
  decide

example : ¬ ∃ rank : Fin 3 → Nat,
    ∀ {a b}, SupportRel cycle a b → rank a < rank b := by
  rintro ⟨rank, h⟩
  have h20 := h (a := (2 : Fin 3)) (b := 0) (by decide)
  have h01 := h (a := (0 : Fin 3)) (b := 1) (by decide)
  have h12 := h (a := (1 : Fin 3)) (b := 2) (by decide)
  omega

end

end STC
