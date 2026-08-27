import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import STC.Foundation.Result

namespace STC.Examples

abbrev Toy := Fin 4

def fin0 : Toy := ⟨0, by decide⟩

def fin1 : Toy := ⟨1, by decide⟩

def fin2 : Toy := ⟨2, by decide⟩

def fin3 : Toy := ⟨3, by decide⟩

def toyClass : Toy → Nat
  | x => if x.val < 2 then 0 else 1

def toyRel (x y : Toy) : Prop := toyClass x = toyClass y

def toyRelSpec : RelSpec Toy where
  rel := toyRel
  refl := by
    intro x
    rfl
  symm := by
    intro x y hxy
    exact hxy.symm
  trans := by
    intro x y z hxy hyz
    exact hxy.trans hyz

instance toyRelDecidable (x y : Toy) : Decidable (toyRel x y) := by
  change Decidable (toyClass x = toyClass y)
  exact inferInstance

instance toyRelSpecDecidable (x y : Toy) : Decidable (toyRelSpec.rel x y) := by
  change Decidable (toyRel x y)
  exact inferInstance

instance toyEqualityDecidable (x y : Toy) : Decidable ((equality Toy).rel x y) := by
  change Decidable (x = y)
  exact inferInstance

instance unitEqualityDecidable (x y : Unit) : Decidable ((equality Unit).rel x y) := by
  change Decidable (x = y)
  exact inferInstance

/- Its self-comparison is pointwise true, but the map does not preserve related inputs. -/
def badMap : Toy → Toy
  | x => if x = fin0 then fin0 else if x = fin1 then fin2 else if x = fin2 then fin2 else fin0

def withinClassSwap : Toy → Toy
  | x => if x = fin0 then fin1 else if x = fin1 then fin0 else if x = fin2 then fin3 else fin2

theorem withinClassSwap_respects : Respects toyRelSpec withinClassSwap := by
  change ∀ x y : Toy, toyRelSpec.rel x y →
    toyRelSpec.rel (withinClassSwap x) (withinClassSwap y)
  decide

theorem withinClassSwap_pointwise_id :
    PointwiseRel toyRelSpec withinClassSwap id := by
  change ∀ x : Toy, toyRelSpec.rel (withinClassSwap x) (id x)
  decide

def pointwiseRelDecidable (f g : Toy → Toy) :
    Decidable (PointwiseRel toyRelSpec f g) := by
  unfold PointwiseRel
  infer_instance

def crossRelDecidable (f g : Toy → Toy) :
    Decidable (CrossRel toyRelSpec f g) := by
  unfold CrossRel
  change Decidable (∀ x y : Toy, toyRelSpec.rel x y →
    toyRelSpec.rel (f x) (g y))
  infer_instance

def effectResultRelDecidable (left right : EffectResult Toy) :
    Decidable (EffectResultRel toyRelSpec left right) := by
  unfold EffectResultRel PointwiseRel
  infer_instance

def equalityEffectResultRelDecidable (left right : EffectResult Toy) :
    Decidable (EffectResultRel (equality Toy) left right) := by
  unfold EffectResultRel PointwiseRel
  infer_instance

def execRelDecidable (left right : ExecResult Toy Unit) :
    Decidable (ExecRel toyRelSpec (equality Unit).rel left right) := by
  cases left <;> cases right
  · unfold ExecRel EffectResultRel PointwiseRel
    infer_instance
  · change Decidable False
    infer_instance
  · change Decidable False
    infer_instance
  · unfold ExecRel FailureRel PointwiseRel
    infer_instance

theorem composed_pointwise_check :
    PointwiseRel toyRelSpec
      (withinClassSwap ∘ withinClassSwap) (id ∘ id) := by
  exact compose_pointwiseRel (R := toyRelSpec)
    (f := withinClassSwap) (g := id) (h := withinClassSwap) (k := id)
    withinClassSwap_respects withinClassSwap_pointwise_id withinClassSwap_pointwise_id

def effectLeft : EffectResult Toy :=
  { state := fin0
    undo := id }

def effectRight : EffectResult Toy :=
  { state := fin1
    undo := id }

def failureLeft : Failure Toy Unit :=
  { error := ()
    boundary := fin0
    prefixUndo := id }

def failureRight : Failure Toy Unit :=
  { error := ()
    boundary := fin1
    prefixUndo := id }

def pointwiseOrientationCheck : Bool :=
  letI : Decidable (PointwiseRel toyRelSpec badMap badMap) :=
    pointwiseRelDecidable badMap badMap
  decide (PointwiseRel toyRelSpec badMap badMap)

def crossOrientationCheck : Bool :=
  letI : Decidable (CrossRel toyRelSpec badMap badMap) :=
    crossRelDecidable badMap badMap
  decide (CrossRel toyRelSpec badMap badMap)

def optionPositiveCheck : Bool :=
  letI : Decidable (OptionRel toyRel (some fin0) (some fin1)) := by
    change Decidable (toyRel fin0 fin1)
    exact toyRelDecidable fin0 fin1
  decide (OptionRel toyRel (some fin0) (some fin1))

def optionMixedCheck : Bool :=
  letI : Decidable (OptionRel toyRel none (some fin0)) := by
    change Decidable False
    infer_instance
  decide (OptionRel toyRel none (some fin0))

def effectResultCheck : Bool :=
  letI : Decidable (EffectResultRel toyRelSpec effectLeft effectRight) :=
    effectResultRelDecidable effectLeft effectRight
  decide (EffectResultRel toyRelSpec effectLeft effectRight)

def failureCheck : Bool :=
  letI : Decidable (FailureRel toyRelSpec (equality Unit).rel failureLeft failureRight) := by
    unfold FailureRel PointwiseRel
    infer_instance
  decide (FailureRel toyRelSpec (equality Unit).rel failureLeft failureRight)

def execSuccessCheck : Bool :=
  letI : Decidable (ExecRel toyRelSpec (equality Unit).rel
      (.success effectLeft) (.success effectRight)) :=
    execRelDecidable (.success effectLeft) (.success effectRight)
  decide (ExecRel toyRelSpec (equality Unit).rel
    (.success effectLeft) (.success effectRight))

def execMixedCheck : Bool :=
  letI : Decidable (ExecRel toyRelSpec (equality Unit).rel
      (.success effectLeft) (.failure failureLeft)) := by
    change Decidable False
    infer_instance
  decide (ExecRel toyRelSpec (equality Unit).rel
    (.success effectLeft) (.failure failureLeft))

def equalityAcceptsReflexiveResult : Bool :=
  letI : Decidable (EffectResultRel (equality Toy) effectLeft effectLeft) :=
    equalityEffectResultRelDecidable effectLeft effectLeft
  decide (EffectResultRel (equality Toy) effectLeft effectLeft)

def equalityRejectsDistinctState : Bool :=
  letI : Decidable (EffectResultRel (equality Toy) effectLeft effectRight) :=
    equalityEffectResultRelDecidable effectLeft effectRight
  decide (EffectResultRel (equality Toy) effectLeft effectRight)

structure CheckReport where
  pointwiseOrientation : Bool
  crossOrientation : Bool
  optionPositive : Bool
  optionMixed : Bool
  effectResult : Bool
  failure : Bool
  execSuccess : Bool
  execMixed : Bool
  equalityReflexive : Bool
  equalityDistinctState : Bool
deriving DecidableEq, Repr

def report : CheckReport :=
  { pointwiseOrientation := pointwiseOrientationCheck
    crossOrientation := crossOrientationCheck
    optionPositive := optionPositiveCheck
    optionMixed := optionMixedCheck
    effectResult := effectResultCheck
    failure := failureCheck
    execSuccess := execSuccessCheck
    execMixed := execMixedCheck
    equalityReflexive := equalityAcceptsReflexiveResult
    equalityDistinctState := equalityRejectsDistinctState }

#eval report

example : report =
    { pointwiseOrientation := true
      crossOrientation := false
      optionPositive := true
      optionMixed := false
      effectResult := true
      failure := true
      execSuccess := true
      execMixed := false
      equalityReflexive := true
      equalityDistinctState := false } := by
  decide

end STC.Examples
