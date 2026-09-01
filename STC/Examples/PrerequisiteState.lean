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

/-! ### Observation-kit closure evidence -/

/-- A concrete equality-based observation kit over the positive carriers. -/
def cellKit : ObservationKit (Registry := PositiveRegistry Nat Nat Bool) (Store := Nat)
    (Life := Bool) (Edit := Bool) (Name := Nat) where
  registry :=
    { rel := fun (r s : PositiveRegistry Nat Nat Bool) => r = s
      refl := by
        intro r
        rfl
      symm := by
        intro r s h
        exact h.symm
      trans := by
        intro r s t h₁ h₂
        exact h₁.trans h₂ }
  committed :=
    { rel := fun (s t : Nat) => s = t
      refl := by
        intro s
        rfl
      symm := by
        intro s t h
        exact h.symm
      trans := by
        intro s t u h₁ h₂
        exact h₁.trans h₂ }
  lifecycle := fun (l r : Bool) => l = r
  controlEdit := fun (l r : Bool) => l = r
  names := fun (l r : Nat) => l = r

def cellProject (c : PositiveContext Nat Nat Nat Bool) : PositiveRegistry Nat Nat Bool :=
  c.registry

def cellCommitted (c : PositiveContext Nat Nat Nat Bool) : Nat :=
  c.ambient

def cellLife (_c : PositiveContext Nat Nat Nat Bool) : Bool := true

def cellEdit (_c : PositiveContext Nat Nat Nat Bool) : Bool := false

def cellName (_c : PositiveContext Nat Nat Nat Bool) : Nat := 0

/-- The lifted observation over the equality kit is reflexive. -/
theorem lifted_kit_refl (c : PositiveContext Nat Nat Nat Bool) :
    liftedStateObs cellKit cellProject cellCommitted cellLife cellEdit cellName c c := by
  exact liftedStateObs_refl cellKit (by intro (l : Bool); rfl) (by intro (e : Bool); rfl)
    (by intro (n : Nat); rfl) cellProject cellCommitted cellLife cellEdit cellName c

/-- The lifted observation over the equality kit is symmetric. -/
theorem lifted_kit_symm {c d : PositiveContext Nat Nat Nat Bool}
    (h : liftedStateObs cellKit cellProject cellCommitted cellLife cellEdit cellName c d) :
    liftedStateObs cellKit cellProject cellCommitted cellLife cellEdit cellName d c := by
  exact liftedStateObs_symm cellKit
    (by intro (l : Bool) (r : Bool) hlr; exact hlr.symm)
    (by intro (l : Bool) (r : Bool) hlr; exact hlr.symm)
    (by intro (l : Nat) (r : Nat) hlr; exact hlr.symm)
    cellProject cellCommitted cellLife cellEdit cellName h

/-- The lifted observation over the equality kit is transitive. -/
theorem lifted_kit_trans {c d e : PositiveContext Nat Nat Nat Bool}
    (h₁ : liftedStateObs cellKit cellProject cellCommitted cellLife cellEdit cellName c d)
    (h₂ : liftedStateObs cellKit cellProject cellCommitted cellLife cellEdit cellName d e) :
    liftedStateObs cellKit cellProject cellCommitted cellLife cellEdit cellName c e := by
  exact liftedStateObs_trans cellKit
    (by intro (l : Bool) (m : Bool) (r : Bool) hlm hmr; exact hlm.trans hmr)
    (by intro (l : Bool) (m : Bool) (r : Bool) hlm hmr; exact hlm.trans hmr)
    (by intro (l : Nat) (m : Nat) (r : Nat) hlm hmr; exact hlm.trans hmr)
    cellProject cellCommitted cellLife cellEdit cellName h₁ h₂

end

end STC.Examples.PrerequisiteState
