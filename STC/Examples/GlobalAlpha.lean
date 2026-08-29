module

public import STC.Control.Alpha

/-!
# Alpha-lane evidence
-/

namespace STC.Examples.GlobalAlpha

open STC STC.Control

@[expose] public section

def action : AlphaAction (Fin 2) Nat where
  act := fun _ n => n
  act_id := by intro n; rfl
  act_comp := by intro χ ψ n; rfl
  act_inv := by intro χ n; rfl

def profile : RuleAlphaProfile (Fin 2) Nat Nat (fun _ _ _ => True) where
  action := action
  renameLabel := fun _ label => label
  equivariant := by intro χ label before after h; exact h

theorem swap_step (χ : Equiv.Perm (Fin 2)) {label : Nat} {before after : Nat}
    (h : (fun _ _ _ : Nat => True) label before after) :
    (fun _ _ _ : Nat => True) (profile.renameLabel χ label)
      (profile.action.act χ before) (profile.action.act χ after) :=
  alpha_step profile χ (label := label) (before := before) (after := after) h

end

end STC.Examples.GlobalAlpha
