module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import STC.Core.Effect

/-!
# Finite executable effect fixtures

A `Fin 3` fixture suite over the shallow effect kernel: lawful `setTo` effects, the
tracked transformation view, the context lift, and the negative countermodel showing that
individual inverse properness and per-run recovery do not imply selected-inverse
coherence.  The final `example`s pin the expected executable report.

## Main declarations

* `Toy`, `toyRelSpec`: the finite carrier and its observational relation;
* `setTo`, `setTo_lawful_eq`, `setTo_lawful_partition`: the lawful setter effect;
* `WeakLawfulAt`, `badCoherence`: the weak law package and its countermodel;
* `EffectReport`, `effectReport`: the aggregated executable report.
-/

namespace STC.Examples.EffectFixture

@[expose] public section

/-! ### The finite toy carrier -/

section ToyFixture

/-- The finite toy state carrier. -/
abbrev Toy := Fin 3

def fin0 : Toy := ⟨0, by decide⟩
def fin1 : Toy := ⟨1, by decide⟩
def fin2 : Toy := ⟨2, by decide⟩

/-- The two-class partition: the first two elements form one observation class. -/
def toyClass (x : Toy) : Nat := if x.val < 2 then 0 else 1

def toyRel (x y : Toy) : Prop := toyClass x = toyClass y

/-- The selected observational relation on `Toy`. -/
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

end ToyFixture

/-! ### Lawful setter effects -/

section SetterEffects

/-- The effect that moves the state to `target` and selects the constant-return inverse. -/
def setTo (target : Toy) : Effect Toy :=
  fun old => { state := target, undo := fun _ => old }

/-- `setTo` is lawful under the equality specialization. -/
theorem setTo_lawful_eq (target : Toy) :
    IsLawfulEffect (equality Toy) (setTo target) := by
  rw [lawful_equality_iff]
  intro input
  rfl

/-- `setTo` is lawful under the observational partition. -/
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

/-- The composed setters are lawful under the partition. -/
theorem composedSet_lawful : IsLawfulEffect toyRelSpec composedSet := by
  exact seqRun_lawful toyRelSpec
    (setTo_lawful_partition fin1) (setTo_lawful_partition fin2)

end SetterEffects

/-! ### Tracked transformations and the context lift -/

section TrackedFixtures

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

end TrackedFixtures

/-! ### The weak-law countermodel -/

section Countermodel

/-- A weak package retaining properness and each run's local recovery, but omitting
related-input coherence of the selected inverse functions. -/
def WeakLawfulAt (R : RelSpec Toy) (e : Effect Toy) : Prop :=
  (∀ input, Respects R (e input).undo) ∧
    (∀ input, R.rel ((e input).undo (e input).state) input)

def badUndo0 : Toy → Toy := fun _ => fin0

def badUndo1 : Toy → Toy :=
  fun x => if toyClass x = 1 then fin2 else fin1

/-- `badUndo0` preserves the partition. -/
theorem badUndo0_respects : Respects toyRelSpec badUndo0 := by
  intro x y hxy
  exact toyRelSpec.refl fin0

/-- `badUndo1` preserves the partition. -/
theorem badUndo1_respects : Respects toyRelSpec badUndo1 := by
  intro x y hxy
  change toyClass (badUndo1 x) = toyClass (badUndo1 y)
  dsimp [badUndo1]
  rw [hxy]

/-- The effect whose selected inverses are individually proper but not coherent. -/
def badCoherence : Effect Toy :=
  fun input =>
    if input = fin0 then
      { state := fin0, undo := badUndo0 }
    else if input = fin1 then
      { state := fin1, undo := badUndo1 }
    else
      { state := input, undo := id }

/-- `badCoherence` satisfies the weak law package. -/
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

/-- `badCoherence` is not lawful: the selected inverses are not pointwise coherent. -/
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

def badSelectedInversePointwiseAtFin2 : Bool :=
  decide (toyRel (badUndo0 fin2) (badUndo1 fin2))

theorem badWeakCheck_eq_true : badWeakCheck = true := rfl
theorem badSelectedInversePointwiseAtFin2_eq_false :
    badSelectedInversePointwiseAtFin2 = false := rfl

end Countermodel

/-! ### The executable report -/

section Report

/-- The aggregated executable fixture report. -/
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
  selectedInversePointwiseAtFin2 : Bool
deriving DecidableEq, Repr

/-- The computed fixture report. -/
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
    selectedInversePointwiseAtFin2 := badSelectedInversePointwiseAtFin2 }

/-- The expected fixture report, pinned by an executable check. -/
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
      selectedInversePointwiseAtFin2 := false } := by
  decide

/-- The composed setters evaluate to the expected effect result. -/
example : composedSet (fin0 : Toy) =
    { state := fin2, undo := (fun _ => fin0) } := by
  apply effectResult_ext
  · rfl
  · funext x
    rfl

/-- The composed setters recover their input up to the partition. -/
theorem composedSet_recovers :
    toyRelSpec.rel ((composedSet fin0).undo (composedSet fin0).state) fin0 := by
  exact (composedSet_lawful).recovers fin0

end Report

end

end STC.Examples.EffectFixture
