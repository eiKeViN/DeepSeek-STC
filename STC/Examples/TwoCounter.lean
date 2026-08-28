module

public import STC.Core.Partial

/-!
# The two-counter failure fixture

The finite P3 failure fixture over two disjoint `Nat` counters: total lawful increments,
the precondition-guarded decrement, the atomic `failIfZero` Toy specialization, the
instance-level independence contract of the two increments, and a foreign-stability
countermodel.  The final `example` pins the expected executable report; all executable
evidence is decidable data.

## Main declarations

* `CounterState`, `inc1`, `inc2`, `dec1`, `dec2`, `failIfZero`: the two-counter carriers;
* `inc1_lawful`, `inc2_lawful`, `failIfZero_atomic`: the K evidence;
* `inc12_independent`: the instance-level operation independence contract;
* `fstProjectOp_not_foreignStable`: the foreign-stability countermodel;
* `CounterFailureReport`, `counterFailureReport`: the pinned executable report.
-/

namespace STC.Examples.TwoCounter

@[expose] public section

/-! ### The two-counter state -/

section Counters

/-- The two-counter state carrier. -/
abbrev CounterState := Nat × Nat

/-- Increment the first counter; the selected inverse decrements it back. -/
def inc1 : Effect CounterState :=
  fun s => { state := (s.1 + 1, s.2), undo := fun t => (t.1 - 1, t.2) }

/-- Increment the second counter; the selected inverse decrements it back. -/
def inc2 : Effect CounterState :=
  fun s => { state := (s.1, s.2 + 1), undo := fun t => (t.1, t.2 - 1) }

/-- Decrement the first counter: defined exactly when it is positive.  The guard is
explicit `Option` undefinedness; on the defined branch the selected inverse is total
because the precondition makes the successor positive. -/
def dec1 : PartialOp CounterState Unit :=
  fun s =>
    if s.1 = 0 then none
    else some { state := (s.1 - 1, s.2), undo := fun t => (t.1 + 1, t.2), outcome := () }

/-- Decrement the second counter: defined exactly when it is positive.  The guard is
explicit `Option` undefinedness; the selected inverse restores the decremented counter. -/
def dec2 : PartialOp CounterState Unit :=
  fun s =>
    if s.2 = 0 then none
    else some { state := (s.1, s.2 - 1), undo := fun t => (t.1, t.2 + 1), outcome := () }

/-- The atomic Toy failure: undefined exactly when the second counter is zero.
Successful runs change nothing and select the identity inverse; atomicity is this
fixture's specialization, not a general failure law. -/
def failIfZero : PartialOp CounterState Unit :=
  fun s =>
    if s.2 = 0 then none else some { state := s, undo := id, outcome := () }

/-- `inc1` is lawful under the equality specialization. -/
theorem inc1_lawful : IsLawfulEffect (equality CounterState) inc1 := by
  rw [lawful_equality_iff]
  intro input
  ext <;> simp [inc1] <;> omega

/-- `inc2` is lawful under the equality specialization. -/
theorem inc2_lawful : IsLawfulEffect (equality CounterState) inc2 := by
  rw [lawful_equality_iff]
  intro input
  ext <;> simp [inc2] <;> omega

/-- `failIfZero` is atomic: successful runs change nothing and select the identity. -/
theorem failIfZero_atomic : ∀ s r, failIfZero s = some r → r.state = s ∧ r.undo = id := by
  intro s r h
  by_cases hz : s.2 = 0
  · simp [failIfZero, hz] at h
  · simp [failIfZero, hz] at h ⊢
    cases h
    constructor <;> rfl

end Counters

/-! ### Independence and foreign stability -/

section Independence

/-- The two disjoint increments satisfy the operation independence contract at the
equality specialization: swapped orders agree on definedness and on the full result
relation, including pointwise-related composed inverses. -/
theorem inc12_independent :
    OperationIndependenceContract (equality CounterState) (equality Unit).rel
      (totalPartialOp inc1) (totalPartialOp inc2) := by
  constructor
  · intro input
    constructor <;> intro h
    · rcases h with ⟨r, hr⟩
      simp [pcompOp, totalPartialOp] at hr
      cases hr
      exact ⟨_, rfl⟩
    · rcases h with ⟨r, hr⟩
      simp [pcompOp, totalPartialOp] at hr
      cases hr
      exact ⟨_, rfl⟩
  · intro input
    simp [pcompOp, totalPartialOp, inc1, inc2, OptionRel, OpResultRel]
    exact ⟨by ext <;> omega, ⟨by
      intro x
      simp only [Function.comp_apply, equality], rfl⟩⟩

/-- A selected inverse that projects away the second counter. -/
def fstProjectUndo : CounterState → CounterState := fun t => (t.1, 0)

/-- The partial operation selecting `fstProjectUndo` on every defined run. -/
def fstProjectOp : PartialOp CounterState Unit :=
  fun s => some { state := s, undo := fstProjectUndo, outcome := () }

/-- Swapping the two counters. -/
def swapCounters : CounterState → CounterState := fun s => (s.2, s.1)

/-- `fstProjectOp` is not foreign-stable for the counter swap: the selected inverse
does not commute with the swap even up to equality. -/
theorem fstProjectOp_not_foreignStable :
    ¬ OperationForeignStability (equality CounterState) fstProjectOp swapCounters := by
  intro h
  have hw := h (1, 2)
    { state := (1, 2), undo := fstProjectUndo, outcome := () } rfl
    (show (equality CounterState).rel (1, 2) (1, 2) from rfl)
  simp [fstProjectUndo, swapCounters] at hw
  have hfst := congrArg Prod.fst hw
  omega

end Independence

/-! ### The executable failure report -/

section Report

/-- A successful `inc1` followed by the failing `failIfZero`: the failure carries the
boundary after the prefix and the prefix inverse. -/
def failAfterInc : ExecResult CounterState Unit :=
  let rInc := inc1 (0, 0)
  match failIfZero rInc.state with
  | none => .failure { error := (), boundary := rInc.state, prefixUndo := rInc.undo }
  | some r => .success { state := r.state, undo := rInc.undo ∘ r.undo }

/-- `inc1` recovers its input. -/
def incRecoverCheck : Bool :=
  decide ((inc1 (0, 0)).undo (inc1 (0, 0)).state = (0, 0))

/-- `failIfZero` is undefined at a zero second counter. -/
def failZeroUndefined : Bool := (failIfZero (2, 0)).isNone

/-- `failIfZero` is defined at a positive second counter. -/
def failNonzeroDefined : Bool := (failIfZero (2, 5)).isSome

/-- A successful `failIfZero` run leaves the state unchanged. -/
def failStateUnchanged : Bool :=
  match failIfZero (2, 5) with
  | some r => decide (r.state = (2, 5))
  | none => false

/-- `dec1` is undefined at a zero first counter. -/
def decZeroUndefined : Bool := (dec1 (0, 5)).isNone

/-- A defined `dec1` run reaches the expected successor. -/
def decDefinedState : Bool :=
  match dec1 (3, 5) with
  | some r => decide (r.state = (2, 5))
  | none => false

/-- `dec2` is undefined at a zero second counter. -/
def dec2ZeroUndefined : Bool := (dec2 (3, 0)).isNone

/-- A defined `dec2` run exposes its successor and selected inverse behavior. -/
def dec2DefinedState : Bool :=
  match dec2 (3, 5) with
  | some r => decide (r.state = (3, 4) ∧ r.undo r.state = (3, 5) ∧ r.outcome = ())
  | none => false

/-- The mixed undefined/defined pair is rejected by the tagged relator. -/
def optionMixedRejected : Bool :=
  letI : Decidable
      (OptionRel (OpResultRel (equality CounterState) (equality Unit).rel)
        (failIfZero (2, 0)) (failIfZero (2, 5))) := by
    change Decidable (OptionRel (OpResultRel (equality CounterState) (equality Unit).rel)
      none (some { state := (2, 5), undo := id, outcome := () }))
    change Decidable False
    infer_instance
  decide (¬ OptionRel (OpResultRel (equality CounterState) (equality Unit).rel)
    (failIfZero (2, 0)) (failIfZero (2, 5)))

/-- The failing prefix retains error, boundary, and the recovering prefix inverse. -/
def failureBoundary : Bool :=
  match failAfterInc with
  | .failure f =>
      decide (f.error = () ∧ f.boundary = (1, 0) ∧ f.prefixUndo f.boundary = (0, 0))
  | .success _ => false

/-- The aggregated executable counter-failure report. -/
structure CounterFailureReport where
  incRecovers : Bool
  failZeroUndefined : Bool
  failNonzeroDefined : Bool
  failStateUnchanged : Bool
  decZeroUndefined : Bool
  decDefinedState : Bool
  dec2ZeroUndefined : Bool
  dec2DefinedState : Bool
  optionMixedRejected : Bool
  failureBoundary : Bool
deriving DecidableEq, Repr

/-- The computed counter-failure report. -/
def counterFailureReport : CounterFailureReport :=
  { incRecovers := incRecoverCheck
    failZeroUndefined := failZeroUndefined
    failNonzeroDefined := failNonzeroDefined
    failStateUnchanged := failStateUnchanged
    decZeroUndefined := decZeroUndefined
    decDefinedState := decDefinedState
    dec2ZeroUndefined := dec2ZeroUndefined
    dec2DefinedState := dec2DefinedState
    optionMixedRejected := optionMixedRejected
    failureBoundary := failureBoundary }

-- No top-level `#eval` (library modules must not evaluate exposed declarations on
-- Windows); the pinned `example` below elaborates the expected report.

/-- The expected counter-failure report, pinned by an executable check. -/
example : counterFailureReport =
    { incRecovers := true
      failZeroUndefined := true
      failNonzeroDefined := true
      failStateUnchanged := true
      decZeroUndefined := true
      decDefinedState := true
      dec2ZeroUndefined := true
      dec2DefinedState := true
      optionMixedRejected := true
      failureBoundary := true } := by
  decide

end Report

end

end STC.Examples.TwoCounter
