module

public import STC.Control.Alpha

/-!
# Alpha-lane evidence
-/

namespace STC.Examples.GlobalAlpha

open STC STC.Control

@[expose] public section

def action : AlphaAction (Fin 2) (Fin 2) where
  act := fun χ n ↦ χ n
  act_id := by intro n; rfl
  act_comp := by intro χ ψ n; rfl
  act_inv := by intro χ n; exact χ.symm_apply_apply n

def profile : RuleAlphaProfile (Fin 2) (Fin 2) Nat
    (fun (_ : Nat) (before after : Fin 2) ↦ after = before) where
  action := action
  renameLabel := fun _ label => label
  equivariant := by
    intro χ label before after h
    exact congrArg χ h

def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

theorem swap_moves_zero : swap 0 = 1 := by decide

theorem swap_step (χ : Equiv.Perm (Fin 2)) {label : Nat} {before after : Fin 2}
    (h : (fun (_ : Nat) (before after : Fin 2) ↦ after = before) label before after) :
    (fun (_ : Nat) (before after : Fin 2) ↦ after = before) (profile.renameLabel χ label)
      (profile.action.act χ before) (profile.action.act χ after) :=
  alpha_step profile χ (label := label) (before := before) (after := after) h

end

end STC.Examples.GlobalAlpha
