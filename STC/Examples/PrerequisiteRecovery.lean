module

public import STC.Core.Effect.Closure
public import STC.Core.Partial.Recovery

/-!
# Recovery prerequisite evidence

Finite declarations exercise generator membership and explicit recovery
contracts. They do not claim lifecycle continuation stability.
-/

namespace STC.Examples.PrerequisiteRecovery

open STC

@[expose] public section

def increment : Transformation Nat := { forward := fun n => n + 1, undo := fun n => n - 1 }
def decrement : Transformation Nat := { forward := fun n => n - 1, undo := fun n => n + 1 }

def generators : Transformation Nat → Prop := fun t => t = increment ∨ t = decrement

theorem increment_generated : Generated generators increment :=
  Generated.generator (Or.inl rfl)

theorem identity_generated : Generated generators Transformation.identity := Generated.identity

def recoveryOp : PartialOp Nat Unit := fun n =>
  some { state := n + 1, undo := fun m => m - 1, outcome := () }

theorem recoveryOp_recovers : OperationRecovers (equality Nat) recoveryOp := by
  intro input result h
  simp [recoveryOp] at h
  subst result
  rfl

def recoverySpec : RecoverySpec (equality Nat) (equality Unit).rel where
  op := recoveryOp
  respects := by
    intro x y h
    cases h
    simp [recoveryOp, OptionRel, OpResultRel]
    constructor
    · rfl
    · constructor
      · intro n
        rfl
      · rfl
  inverseStable := by
    intro input result h
    simp [recoveryOp] at h
    subst result
    intro x y hxy
    cases hxy
    rfl
  recovers := recoveryOp_recovers

theorem recovery_checked (n : Nat) :
    ∃ result, recoverySpec.op n = some result ∧
      result.undo result.state = n := by
  refine ⟨{ state := n + 1, undo := fun m => m - 1, outcome := () }, ?_, ?_⟩
  · rfl
  · simp

/-! ### Two independent operations: counter increment and flag flip -/

abbrev CounterState := Nat × Bool

def counterIncrement : Transformation CounterState :=
  { forward := fun s => (s.1 + 1, s.2), undo := fun s => (s.1 - 1, s.2) }

def flagFlip : Transformation CounterState :=
  { forward := fun s => (s.1, !s.2), undo := fun s => (s.1, !s.2) }

def incrementOp : Effect CounterState :=
  uniformEffect counterIncrement

def flipOp : Effect CounterState :=
  uniformEffect flagFlip

def countDec : CounterState → CounterState :=
  counterIncrement.undo

def flagNot : CounterState → CounterState :=
  flagFlip.undo

/-- The increment effect is lawful at equality. -/
theorem incrementOp_lawful : IsLawfulEffect (equality CounterState) incrementOp := by
  apply uniformEffect_lawful
  · intro x y h
    cases h
    rfl
  · intro x y h
    cases h
    rfl
  · intro input
    ext
    · exact Nat.add_sub_cancel_right input.1 1
    · rfl

/-- The flip effect is lawful at equality. -/
theorem flipOp_lawful : IsLawfulEffect (equality CounterState) flipOp := by
  apply uniformEffect_lawful
  · intro x y h
    cases h
    rfl
  · intro x y h
    cases h
    rfl
  · intro input
    ext
    · rfl
    · exact Bool.not_not input.2

/-- The two operations are independent in the audited effect-level contract. -/
theorem increment_flip_independent :
    EffectIndependence (equality CounterState) incrementOp flipOp := by
  intro input
  constructor
  · rfl
  · intro s
    rfl

/-- The increment inverse commutes with the flip forward map. -/
theorem countDec_flipForward_commutes :
    CrossRel (equality CounterState) (countDec ∘ flagFlip.forward)
      (flagFlip.forward ∘ countDec) := by
  intro x y h
  cases h
  rfl

/-- The flip inverse commutes with the increment forward map. -/
theorem flagNot_incForward_commutes :
    CrossRel (equality CounterState) (flagNot ∘ counterIncrement.forward)
      (counterIncrement.forward ∘ flagNot) := by
  intro x y h
  cases h
  rfl

/-- T20 at the finite instance: removing the increment after a later flip reaches the
state the flip alone reaches. -/
theorem selective_removal_counter_flip (input : CounterState) :
    (incrementOp input).undo ((runSequence [flipOp] (incrementOp input).state).state) =
      (runSequence [flipOp] input).state :=
  selective_removal (equality CounterState) incrementOp [flipOp]
    incrementOp_lawful
    (fun (h : Effect CounterState) (hmem : h ∈ [flipOp]) => by
      have heq : h = flipOp := by simpa using hmem
      simpa [heq] using flipOp_lawful)
    (fun (h : Effect CounterState) (hmem : h ∈ [flipOp]) (input' : CounterState) => by
      have heq : h = flipOp := by simpa using hmem
      subst heq
      intro x y hxy
      cases hxy
      rfl)
    input

/-- The pairwise inverse-commutation law for the two-operation inverse word. -/
theorem inverse_word_commutes :
    ∀ {g h : CounterState → CounterState},
      g ∈ inverseWord [incrementOp, flipOp] (5, true) →
      h ∈ inverseWord [incrementOp, flipOp] (5, true) →
      CrossRel (equality CounterState) (g ∘ h) (h ∘ g) := by
  intro g h hg hh
  simp [inverseWord, incrementOp, flipOp, uniformEffect, counterIncrement, flagFlip] at hg hh
  rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
  · intro x y hxy
    cases hxy
    rfl
  · intro x y hxy
    cases hxy
    rfl
  · intro x y hxy
    cases hxy
    rfl
  · intro x y hxy
    cases hxy
    rfl

/-- C21 at the finite instance: the two inverses applied in swapped order still recover
the input, through the checked `List.Perm` theorem. -/
theorem arbitrary_order_recovery_counter :
    applyWord [countDec, flagNot]
        ((runSequence [incrementOp, flipOp] (5, true)).state) = (5, true) := by
  have hperm : List.Perm [countDec, flagNot]
      (inverseWord [incrementOp, flipOp] (5, true)).reverse := by
    simp [inverseWord, incrementOp, flipOp, uniformEffect, countDec, flagNot,
      counterIncrement, flagFlip]
    exact List.Perm.swap flagNot countDec []
  have hlaw : ∀ (e : Effect CounterState),
      e ∈ [incrementOp, flipOp] → IsLawfulEffect (equality CounterState) e := by
    intro e he
    simp at he
    rcases he with rfl | rfl
    · exact incrementOp_lawful
    · exact flipOp_lawful
  exact arbitrary_order_recovery (equality CounterState) [incrementOp, flipOp]
    hlaw (5, true) inverse_word_commutes hperm

/-! ### Pinned finite checks -/

/-- The forward run of the two operations. -/
example : (runSequence [incrementOp, flipOp] (5, true)).state = (6, false) := by
  decide

/-- The LIFO reverse-order recovery. -/
example :
    ((runSequence [incrementOp, flipOp] (5, true)).undo
        ((runSequence [incrementOp, flipOp] (5, true)).state)) = (5, true) := by
  decide

/-- The T20 removal equation at a concrete input. -/
example : countDec ((runSequence [flipOp] (incrementOp (3, true)).state).state) =
    (runSequence [flipOp] (3, true)).state := by
  decide

/-- Swapped-order inverse application still recovers. -/
example : applyWord [flagNot, countDec]
    ((runSequence [incrementOp, flipOp] (5, true)).state) = (5, true) := by
  decide

end

end STC.Examples.PrerequisiteRecovery
