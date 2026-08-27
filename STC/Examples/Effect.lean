import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import STC.Core.Effect

namespace STC.Examples

abbrev Toy := Fin 3

def fin0 : Toy := ⟨0, by decide⟩
def fin1 : Toy := ⟨1, by decide⟩
def fin2 : Toy := ⟨2, by decide⟩

def toyClass (x : Toy) : Nat := if x.val < 2 then 0 else 1

def toyRel (x y : Toy) : Prop := toyClass x = toyClass y

def toyRelSpec : RelSpec Toy where
  rel := toyRel
  refl := by intro x; rfl
  symm := by intro x y h; exact h.symm
  trans := by intro x y z hxy hyz; exact hxy.trans hyz

instance toyRelDecidable (x y : Toy) : Decidable (toyRel x y) := by
  change Decidable (toyClass x = toyClass y)
  exact inferInstance

instance toyRelSpecDecidable (x y : Toy) : Decidable (toyRelSpec.rel x y) := by
  change Decidable (toyRel x y)
  exact inferInstance

instance toyEqualityDecidable (x y : Toy) : Decidable ((equality Toy).rel x y) := by
  change Decidable (x = y)
  exact inferInstance

def setTo (target : Toy) : Effect Toy :=
  fun old => { state := target, undo := fun _ => old }

theorem setTo_lawful_eq (target : Toy) :
    IsLawfulEffect (equality Toy) (setTo target) := by
  rw [lawful_equality_iff]
  intro input
  rfl

theorem setTo_lawful_partition (target : Toy) :
    IsLawfulEffect toyRelSpec (setTo target) := by
  constructor
  · intro x y hxy
    exact ⟨toyRelSpec.refl target, by
      intro z
      exact hxy⟩
  · intro input x y hxy
    rfl
  · intro input
    exact toyRelSpec.refl input

def setTo01 : Effect Toy := setTo fin1
def setTo02 : Effect Toy := setTo fin2
def composedSet : Effect Toy := seqRun setTo01 setTo02

theorem composedSet_lawful : IsLawfulEffect toyRelSpec composedSet := by
  exact seqRun_lawful toyRelSpec
    (setTo_lawful_partition fin1) (setTo_lawful_partition fin2)

def swap01 : Toy → Toy
  | x => if x = fin0 then fin1 else if x = fin1 then fin0 else fin2

def swap12 : Toy → Toy
  | x => if x = fin1 then fin2 else if x = fin2 then fin1 else fin0

def earlierTransform : Transformation Toy :=
  { forward := swap01, undo := swap01 }

def laterTransform : Transformation Toy :=
  { forward := swap12, undo := swap12 }

def twistedTransform : Transformation Toy :=
  Transformation.twisted laterTransform earlierTransform

def trackedTwisted : EffectContext Toy :=
  track twistedTransform (fin0, id)

def recoveredTwisted : EffectContext Toy := recover trackedTwisted

def liftedSet : Effect (EffectContext Toy) := liftEffect setTo02

def liftedRun : EffectResult (EffectContext Toy) := liftedSet (fin0, id)

def liftedRecovered : EffectContext Toy := liftedRun.undo liftedRun.state

/- A weak package retaining properness and each run's local recovery, but omitting
   related-input coherence of the selected inverse functions. -/
def WeakLawfulAt (R : RelSpec Toy) (e : Effect Toy) : Prop :=
  (∀ input, Respects R (e input).undo) ∧
    (∀ input, R.rel ((e input).undo (e input).state) input)

def badUndo0 : Toy → Toy := fun _ => fin0

def badUndo1 : Toy → Toy :=
  fun x => if toyClass x = 1 then fin2 else fin1

theorem badUndo0_respects : Respects toyRelSpec badUndo0 := by
  intro x y hxy
  exact toyRelSpec.refl fin0

theorem badUndo1_respects : Respects toyRelSpec badUndo1 := by
  intro x y hxy
  change toyClass (badUndo1 x) = toyClass (badUndo1 y)
  dsimp [badUndo1]
  rw [hxy]

def badCoherence : Effect Toy :=
  fun input =>
    if input = fin0 then
      { state := fin0, undo := badUndo0 }
    else if input = fin1 then
      { state := fin1, undo := badUndo1 }
    else
      { state := input, undo := id }

theorem badCoherence_weak : WeakLawfulAt toyRelSpec badCoherence := by
  constructor
  · intro input
    by_cases h0 : input = fin0
    · subst input
      simpa [badCoherence] using badUndo0_respects
    · by_cases h1 : input = fin1
      · subst input
        simpa [badCoherence, fin0, fin1] using badUndo1_respects
      · simp [badCoherence, h0, h1]
  · intro input
    by_cases h0 : input = fin0
    · subst input; rfl
    · by_cases h1 : input = fin1
      · subst input; rfl
      · simp [badCoherence, h0, h1]
        exact toyRelSpec.refl input

theorem badCoherence_not_lawful :
    ¬ IsLawfulEffect toyRelSpec badCoherence := by
  intro h
  have hrun := h.run_respects (x := fin0) (y := fin1) (by decide)
  have hpoint := hrun.2 fin2
  simp [badCoherence, badUndo0, badUndo1, toyRelSpec,
    toyRel, toyClass, fin0, fin1, fin2] at hpoint

def badWeakCheck : Bool :=
  letI : Decidable (WeakLawfulAt toyRelSpec badCoherence) := by
    unfold WeakLawfulAt Respects RespectsOn
    infer_instance
  decide (WeakLawfulAt toyRelSpec badCoherence)

def badLawfulCheck : Bool :=
  decide (toyRel (badUndo0 fin2) (badUndo1 fin2))

theorem badWeakCheck_eq_true : badWeakCheck = true := rfl
theorem badLawfulCheck_eq_false : badLawfulCheck = false := rfl

structure EffectReport where
  composedFinal : Toy
  composedRecovered : Toy
  wrongOrderRecovered : Toy
  twistedForward : Toy
  twistedUndoApplied : Toy
  trackedState : Toy
  trackedAccumulatorApplied : Toy
  recoveredState : Toy
  liftedState : Toy
  liftedRecoveredState : Toy
  liftedAccumulatorApplied : Toy
  weakSelectedInversePackage : Bool
  fullSelectedInverseLaw : Bool
deriving DecidableEq, Repr

def effectReport : EffectReport :=
  let first := setTo01 fin0
  let second := setTo02 first.state
  { composedFinal := (composedSet fin0).state
    composedRecovered := (composedSet fin0).undo (composedSet fin0).state
    wrongOrderRecovered := second.undo (first.undo second.state)
    twistedForward := twistedTransform.forward fin0
    twistedUndoApplied := twistedTransform.undo (twistedTransform.forward fin0)
    trackedState := trackedTwisted.1
    trackedAccumulatorApplied := trackedTwisted.2 fin2
    recoveredState := recoveredTwisted.1
    liftedState := liftedRun.state.1
    liftedRecoveredState := liftedRecovered.1
    liftedAccumulatorApplied := liftedRecovered.2 fin2
    weakSelectedInversePackage := badWeakCheck
    fullSelectedInverseLaw := badLawfulCheck }

#eval effectReport

example : effectReport =
    { composedFinal := fin2
      composedRecovered := fin0
      wrongOrderRecovered := fin1
      twistedForward := fin2
      twistedUndoApplied := fin0
      trackedState := fin2
      trackedAccumulatorApplied := fin0
      recoveredState := fin0
      liftedState := fin2
      liftedRecoveredState := fin0
      liftedAccumulatorApplied := fin0
      weakSelectedInversePackage := true
      fullSelectedInverseLaw := false } := by
  decide

example : composedSet (fin0 : Toy) =
    { state := fin2, undo := (fun _ => fin0) } := by
  apply effectResult_ext
  · rfl
  · funext x
    rfl

theorem composedSet_recovers :
    toyRelSpec.rel ((composedSet fin0).undo (composedSet fin0).state) fin0 := by
  exact (composedSet_lawful).recovers fin0

end STC.Examples
