module

public import STC.Alpha.Transport
public import STC.Core.Iterator
public import STC.Examples.TwoCounter

/-!
# The nested-iterator vertical slice

The P4 nested-iterator fixture over the two-counter state: a multi-stage success
iterator, a failing stage with a visibly retained prefix undo, rank-decreasing nested
continuations, the instance-level stage witness, and the pinned executable report.
P4 owns the iterator/failure transport checks; the later P7 owner extends this file.

The report is pinned by equation-based trace proofs rather than `decide` over
`execFrom`: the well-founded `execFrom` does not reduce in the kernel's `Decidable`
computation.

## Main declarations

* `Control`, `counterRun`, `counterRank`, `counterIterator`: the success machine;
* `failingRun`, `failingIterator`: the failing machine;
* `TwoCounterControl`, `twoCounterIterator`, `TwoCounterFailureControl`,
  `twoCounterFailureIterator`: the additive P7 paths;
* `counterStageWitness`: the instance-level stage witness (`K`);
* `execCount0`–`execCount3`, `counterExec_eq`, `failingExec_eq`, `stageCount_eq`:
  the computed traces;
* `twoCounterSuccessExec_eq`, `twoCounterFailureExec_eq`, and their stage-count equations:
  the P7 equation-pinned traces;
* `twoCounterAlphaExec_transport`, `twoCounterAlphaSuccess_transport`, and the
  alpha-labelled boundary checks;
* `stageMixed_not_rel`, `execSuccess_refl`: the relation checks (`K`);
* `SliceReport`, `sliceReport`: the pinned executable report (`E`).
-/

namespace STC.Examples.VerticalSlice

open STC.Examples.TwoCounter

@[expose] public section

/-! ### The nested continuation machine -/

section Machine

/-- The external control codes of the slice: start the countdown, or continue from `n`.
Each yielded continuation carries a strictly smaller countdown. -/
inductive Control where
  | start
  | count (n : Nat)
deriving DecidableEq

/-- Every stage increments the first counter; the countdown halts at zero. -/
def counterRun : Control → CounterState → StageResult CounterState Unit Control
  | .start, s => .yield (inc1 s) (.count 3)
  | .count n, s =>
      if n = 0 then .halt (inc1 s) else .yield (inc1 s) (.count (n - 1))

/-- The rank of a control code: `start` is outermost, every countdown step lowers it. -/
def counterRank : Control → Nat
  | .start => 5
  | .count n => n + 1

/-- The rank certificate: every yielded continuation has strictly smaller rank. -/
theorem counterNextLt : ∀ {q s result q'},
    counterRun q s = .yield result q' → counterRank q' < counterRank q := by
  intro q s result q' h
  cases q with
  | start =>
      simp only [counterRun, counterRank] at h ⊢
      cases h
      decide
  | count n =>
      simp only [counterRun] at h
      by_cases hn : n = 0
      · simp [hn] at h
      · simp only [hn] at h
        cases h
        simp only [counterRank]
        omega

/-- The success iterator: five stages from `start`, halting at the zero countdown. -/
def counterIterator : RankedIterator CounterState Unit Control where
  root := .start
  rank := counterRank
  run := counterRun
  next_lt := counterNextLt

/-- The failing variant: a stage whose second counter is zero raises before the step. -/
def failingRun : Control → CounterState → StageResult CounterState Unit Control
  | .start, s => .yield (inc1 s) (.count 3)
  | .count n, s =>
      if s.2 = 0 then .raise ()
      else if n = 0 then .halt (inc1 s) else .yield (inc1 s) (.count (n - 1))

/-- The rank certificate of the failing machine. -/
theorem failingNextLt : ∀ {q s result q'},
    failingRun q s = .yield result q' → counterRank q' < counterRank q := by
  intro q s result q' h
  cases q with
  | start =>
      simp only [failingRun, counterRank] at h ⊢
      cases h
      decide
  | count n =>
      simp only [failingRun] at h
      have hs : s.2 ≠ 0 := by
        intro hs0
        simp [hs0] at h
      by_cases hn : n = 0
      · simp [hs, hn] at h
      · simp only [hs, hn] at h
        cases h
        simp only [counterRank]
        omega

/-- The failing iterator over the same ranked control carrier. -/
def failingIterator : RankedIterator CounterState Unit Control where
  root := .start
  rank := counterRank
  run := failingRun
  next_lt := failingNextLt

/-- Every stage of the success machine recovers locally and selects only
relation-preserving inverses: the instance-level stage witness. -/
theorem counterStageWitness : StageWitness (equality CounterState) counterIterator := by
  constructor
  intro q input
  cases q with
  | start =>
      simp only [counterIterator, counterRun]
      constructor
      · exact (inc1_lawful).recovers input
      · intro x y h
        cases h
        rfl
  | count n =>
      by_cases hn : n = 0
      · simp only [counterIterator, counterRun, hn]
        constructor
        · exact (inc1_lawful).recovers input
        · intro x y h
          cases h
          rfl
      · simp only [counterIterator, counterRun, hn]
        constructor
        · exact (inc1_lawful).recovers input
        · intro x y h
          cases h
          rfl

end Machine

/-! ### The P7 two-counter paths -/

section TwoCounterPaths

/-- Control codes for the additive two-counter success path. -/
inductive TwoCounterControl where
  | start
  | afterInc1
  | afterInc2
deriving DecidableEq, Repr

/-- The success path applies `inc1`, then `inc2`, and finally halts with identity. -/
def twoCounterRun : TwoCounterControl → CounterState →
    StageResult CounterState Unit TwoCounterControl
  | .start, state => .yield (inc1 state) .afterInc1
  | .afterInc1, state => .yield (inc2 state) .afterInc2
  | .afterInc2, state => .halt (identityEffect state)

/-- The rank certificate for the P7 success path. -/
def twoCounterRank : TwoCounterControl → Nat
  | .start => 3
  | .afterInc1 => 2
  | .afterInc2 => 0

/-- Every yielded P7 success continuation strictly decreases `twoCounterRank`. -/
theorem twoCounterNextLt : ∀ {q state result next},
    twoCounterRun q state = .yield result next → twoCounterRank next < twoCounterRank q := by
  intro q state result next h
  cases q with
  | start =>
      simp only [twoCounterRun, twoCounterRank] at h ⊢
      cases h
      decide
  | afterInc1 =>
      simp only [twoCounterRun, twoCounterRank] at h ⊢
      cases h
      decide
  | afterInc2 => simp [twoCounterRun] at h

/-- The ranked P7 success iterator. -/
def twoCounterIterator : RankedIterator CounterState Unit TwoCounterControl where
  root := .start
  rank := twoCounterRank
  run := twoCounterRun
  next_lt := twoCounterNextLt

/-- The failure-path control codes: increment once, then run `failIfZero`. -/
inductive TwoCounterFailureControl where
  | start
  | check
deriving DecidableEq, Repr

/-- The P7 failure path applies `inc1` and then exposes `failIfZero` at the boundary. -/
def twoCounterFailureRun : TwoCounterFailureControl → CounterState →
    StageResult CounterState Unit TwoCounterFailureControl
  | .start, state => .yield (inc1 state) .check
  | .check, state =>
      match failIfZero state with
      | none => .raise ()
      | some result => .halt { state := result.state, undo := result.undo }

/-- The rank certificate for the P7 failure path. -/
def twoCounterFailureRank : TwoCounterFailureControl → Nat
  | .start => 2
  | .check => 0

/-- Every yielded P7 failure continuation strictly decreases its rank. -/
theorem twoCounterFailureNextLt : ∀ {q state result next},
    twoCounterFailureRun q state = .yield result next →
      twoCounterFailureRank next < twoCounterFailureRank q := by
  intro q state result next h
  cases q with
  | start =>
      simp only [twoCounterFailureRun, twoCounterFailureRank] at h ⊢
      cases h
      decide
  | check =>
      cases hrun : failIfZero state with
      | none => simp [twoCounterFailureRun, hrun] at h
      | some result => simp [twoCounterFailureRun, hrun] at h

/-- The ranked P7 failure iterator. -/
def twoCounterFailureIterator :
    RankedIterator CounterState Unit TwoCounterFailureControl where
  root := .start
  rank := twoCounterFailureRank
  run := twoCounterFailureRun
  next_lt := twoCounterFailureNextLt

/-- Every successful stage of the P7 success iterator recovers locally. -/
theorem twoCounterStageWitness :
    StageWitness (equality CounterState) twoCounterIterator := by
  constructor
  intro q input
  cases q with
  | start =>
      simp only [twoCounterIterator, twoCounterRun]
      exact ⟨inc1_lawful.recovers input, inc1_lawful.undo_respects input⟩
  | afterInc1 =>
      simp only [twoCounterIterator, twoCounterRun]
      exact ⟨inc2_lawful.recovers input, inc2_lawful.undo_respects input⟩
  | afterInc2 =>
      simp only [twoCounterIterator, twoCounterRun]
      exact ⟨(identityEffect_lawful (equality CounterState)).recovers input,
        (identityEffect_lawful (equality CounterState)).undo_respects input⟩

/-- Every successful stage of the P7 failure iterator recovers locally; the `raise` branch
is intentionally discharged by `True`, as required by the failure carrier. -/
theorem twoCounterFailureStageWitness :
    StageWitness (equality CounterState) twoCounterFailureIterator := by
  constructor
  intro q input
  cases q with
  | start =>
      simp only [twoCounterFailureIterator, twoCounterFailureRun]
      exact ⟨inc1_lawful.recovers input, inc1_lawful.undo_respects input⟩
  | check =>
      by_cases hz : input.2 = 0
      · simp [twoCounterFailureIterator, twoCounterFailureRun, failIfZero, hz]
      · simp [twoCounterFailureIterator, twoCounterFailureRun, failIfZero, hz]
        exact ⟨(identityEffect_lawful (equality CounterState)).recovers input,
          (identityEffect_lawful (equality CounterState)).undo_respects input⟩

end TwoCounterPaths

/-! ### The computed execution traces -/

section Traces

/-- The states reached by the success trace. -/
def s0 : CounterState := (0, 7)
def s1 : CounterState := (inc1 s0).state
def s2 : CounterState := (inc1 s1).state
def s3 : CounterState := (inc1 s2).state
def s4 : CounterState := (inc1 s3).state

/-- The final stage halts and returns its increment. -/
theorem execCount0 :
    execFrom counterIterator (.count 0) s4 =
      .success ⟨(inc1 s4).state, (inc1 s4).undo⟩ := by
  rw [execFrom_halt (it := counterIterator)
    (h := (show counterIterator.run (.count 0) s4 = .halt (inc1 s4) from rfl))]

/-- The one-before-final stage yields into `execCount0` and prepends its inverse. -/
theorem execCount1 :
    execFrom counterIterator (.count 1) s3 =
      .success ⟨(inc1 s4).state, (inc1 s3).undo ∘ (inc1 s4).undo⟩ := by
  rw [execFrom_yield_success (it := counterIterator)
    (hyield := (show counterIterator.run (.count 1) s3 = .yield (inc1 s3) (.count 0)
      from rfl))
    (hinner := execCount0)]

/-- The third stage yields into `execCount1` and prepends its inverse. -/
theorem execCount2 :
    execFrom counterIterator (.count 2) s2 =
      .success ⟨(inc1 s4).state, (inc1 s2).undo ∘ (inc1 s3).undo ∘ (inc1 s4).undo⟩ := by
  rw [execFrom_yield_success (it := counterIterator)
    (hyield := (show counterIterator.run (.count 2) s2 = .yield (inc1 s2) (.count 1)
      from rfl))
    (hinner := execCount1)]

/-- The second stage yields into `execCount2` and prepends its inverse. -/
theorem execCount3 :
    execFrom counterIterator (.count 3) s1 =
      .success ⟨(inc1 s4).state,
        (inc1 s1).undo ∘ (inc1 s2).undo ∘ (inc1 s3).undo ∘ (inc1 s4).undo⟩ := by
  rw [execFrom_yield_success (it := counterIterator)
    (hyield := (show counterIterator.run (.count 3) s1 = .yield (inc1 s1) (.count 2)
      from rfl))
    (hinner := execCount2)]

/-- The success trace from `(0, 7)` runs five stages and composes the five selected
inverses in LIFO order. -/
theorem counterExec_eq :
    execFrom counterIterator .start s0 =
      .success { state := (5, 7), undo := fun t => (t.1 - 5, t.2) } := by
  rw [execFrom_yield_success (it := counterIterator)
    (hyield := (show counterIterator.run .start s0 = .yield (inc1 s0) (.count 3)
      from rfl))
    (hinner := execCount3)]
  apply congrArg (ExecResult.success : EffectResult CounterState → ExecResult CounterState Unit)
  apply effectResult_ext
  · rfl
  · funext t
    ext <;> simp only [Function.comp_apply, inc1]
    all_goals omega

/-- The failing trace from `(0, 0)` raises after the first successful stage, retaining
the boundary and the prefix inverse. -/
theorem failingExec_eq :
    execFrom failingIterator .start (0, 0) =
      .failure { error := (), boundary := (1, 0), prefixUndo := (inc1 (0, 0)).undo } := by
  rw [execFrom_yield_failure (it := failingIterator)
    (hyield := (show failingIterator.run .start (0, 0) =
      .yield (inc1 (0, 0)) (.count 3) from rfl))
    (hinner := by
      rw [execFrom_raise (it := failingIterator)
        (h := (show failingIterator.run (.count 3) ((inc1 (0, 0)).state) = .raise ()
          from rfl))])]
  simp only [inc1]
  rfl

/-- The success trace uses exactly five stages. -/
theorem stageCount_eq : stageCountFrom counterIterator .start (0, 7) = 5 := by
  unfold stageCountFrom
  rw [show counterIterator.run .start (0, 7) = .yield (inc1 (0, 7)) (.count 3) from rfl]
  simp only []
  unfold stageCountFrom
  rw [show counterIterator.run (.count 3) (inc1 (0, 7)).state =
      .yield (inc1 ((inc1 (0, 7)).state)) (.count 2) from rfl]
  simp only []
  unfold stageCountFrom
  rw [show counterIterator.run (.count 2) (inc1 ((inc1 (0, 7)).state)).state =
      .yield (inc1 ((inc1 ((inc1 (0, 7)).state)).state)) (.count 1) from rfl]
  simp only []
  unfold stageCountFrom
  rw [show counterIterator.run (.count 1) (inc1 ((inc1 ((inc1 (0, 7)).state)).state)).state =
      .yield (inc1 ((inc1 ((inc1 ((inc1 (0, 7)).state)).state)).state)) (.count 0) from rfl]
  simp only []
  unfold stageCountFrom
  rw [show counterIterator.run (.count 0) (inc1 ((inc1 ((inc1 ((inc1 (0, 7)).state)).state)).state)).state =
      .halt (inc1 ((inc1 ((inc1 ((inc1 ((inc1 (0, 7)).state)).state)).state)).state)) from rfl]
  simp only []

end Traces

/-! ### P7 two-counter equations -/

section TwoCounterTraces

/-- The canonical P7 success input and the two intermediate states. -/
def twoCounterS0 : CounterState := (0, 0)
def twoCounterS1 : CounterState := (inc1 twoCounterS0).state
def twoCounterS2 : CounterState := (inc2 twoCounterS1).state

/-- The final halt stage of the P7 success path. -/
theorem twoCounterExec_afterInc2 :
    execFrom twoCounterIterator .afterInc2 twoCounterS2 =
      .success (identityEffect twoCounterS2) := by
  rw [execFrom_halt (it := twoCounterIterator)
    (h := (show twoCounterIterator.run .afterInc2 twoCounterS2 =
      .halt (identityEffect twoCounterS2) from rfl))]

/-- The second success stage yields into the final halt stage. -/
theorem twoCounterExec_afterInc1 :
    execFrom twoCounterIterator .afterInc1 twoCounterS1 =
      .success { state := twoCounterS2, undo := (inc2 twoCounterS1).undo } := by
  rw [execFrom_yield_success (it := twoCounterIterator)
    (hyield := (show twoCounterIterator.run .afterInc1 twoCounterS1 =
      .yield (inc2 twoCounterS1) .afterInc2 from rfl))
    (hinner := twoCounterExec_afterInc2)]
  rfl

/-- The complete P7 success path reaches `(1, 1)` with both selected inverses. -/
theorem twoCounterSuccessExec_eq :
    execFrom twoCounterIterator .start twoCounterS0 =
      .success { state := (1, 1), undo := fun value => (value.1 - 1, value.2 - 1) } := by
  rw [execFrom_yield_success (it := twoCounterIterator)
    (hyield := (show twoCounterIterator.run .start twoCounterS0 =
      .yield (inc1 twoCounterS0) .afterInc1 from rfl))
    (hinner := twoCounterExec_afterInc1)]
  apply congrArg (ExecResult.success : EffectResult CounterState → ExecResult CounterState Unit)
  apply effectResult_ext
  · rfl
  · funext value
    ext <;> simp [twoCounterS0, twoCounterS1, inc1, inc2, Function.comp_apply]

/-- The `failIfZero` stage raises at the canonical `(1, 0)` boundary. -/
theorem twoCounterFailureCheckExec_eq :
    execFrom twoCounterFailureIterator .check (1, 0) =
      .failure { error := (), boundary := (1, 0), prefixUndo := id } := by
  rw [execFrom_raise (it := twoCounterFailureIterator)
    (h := (show twoCounterFailureIterator.run .check (1, 0) = .raise () by
      simp [twoCounterFailureIterator, twoCounterFailureRun, failIfZero]))]

/-- The complete P7 failure path preserves the successful `inc1` prefix inverse. -/
theorem twoCounterFailureExec_eq :
    execFrom twoCounterFailureIterator .start twoCounterS0 =
      .failure { error := (), boundary := (1, 0), prefixUndo := (inc1 twoCounterS0).undo } := by
  rw [execFrom_yield_failure (it := twoCounterFailureIterator)
    (hyield := (show twoCounterFailureIterator.run .start twoCounterS0 =
      .yield (inc1 twoCounterS0) .check from rfl))
    (hinner := twoCounterFailureCheckExec_eq)]
  rfl

/-- The success path uses three ranked stages. -/
theorem twoCounterSuccessStageCount_eq :
    stageCountFrom twoCounterIterator .start twoCounterS0 = 3 := by
  unfold stageCountFrom
  rw [show twoCounterIterator.run .start twoCounterS0 =
      .yield (inc1 twoCounterS0) .afterInc1 from rfl]
  simp only []
  change 1 + stageCountFrom twoCounterIterator .afterInc1 twoCounterS1 = 3
  unfold stageCountFrom
  rw [show twoCounterIterator.run .afterInc1 twoCounterS1 =
      .yield (inc2 twoCounterS1) .afterInc2 from rfl]
  simp only []
  change 1 + (1 + stageCountFrom twoCounterIterator .afterInc2 twoCounterS2) = 3
  unfold stageCountFrom
  rw [show twoCounterIterator.run .afterInc2 twoCounterS2 =
      .halt (identityEffect twoCounterS2) from rfl]
  simp only []

/-- The failure path uses one successful stage and one raising stage. -/
theorem twoCounterFailureStageCount_eq :
    stageCountFrom twoCounterFailureIterator .start twoCounterS0 = 2 := by
  unfold stageCountFrom
  rw [show twoCounterFailureIterator.run .start twoCounterS0 =
      .yield (inc1 twoCounterS0) .check from rfl]
  simp only []
  change 1 + stageCountFrom twoCounterFailureIterator .check (1, 0) = 2
  unfold stageCountFrom
  rw [show twoCounterFailureIterator.run .check (1, 0) = .raise () by
      simp [twoCounterFailureIterator, twoCounterFailureRun, failIfZero]]
  simp only []

end TwoCounterTraces

/-! ### P7 integrated recovery corollaries -/

section IntegratedRecovery

/-- The generic execution recovery theorem discharges the P7 success path. -/
theorem twoCounterSuccess_recovery :
    (equality CounterState).rel
      ((fun value : CounterState => (value.1 - 1, value.2 - 1)) (1, 1)) twoCounterS0 := by
  exact execFrom_success_recovers (equality CounterState) twoCounterIterator
    twoCounterStageWitness.stage twoCounterSuccessExec_eq

/-- The generic execution recovery theorem discharges the P7 failure prefix boundary. -/
theorem twoCounterFailure_recovery :
    (equality CounterState).rel ((inc1 twoCounterS0).undo (1, 0)) twoCounterS0 := by
  exact execFrom_failure_recovers (equality CounterState) twoCounterFailureIterator
    twoCounterFailureStageWitness.stage twoCounterFailureExec_eq

end IntegratedRecovery

/-! ### P7 alpha-labelled regression -/

section AlphaRegression

/-- The finite non-identity permutation used by the P7 trace regression. -/
def twoCounterSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- The name-neutral state action for the P7 iterator.  Name-bearing data is carried by
the explicit `NameTrace` below, matching the P6 neutral-payload boundary. -/
def twoCounterAlphaAction : AlphaAction (Fin 2) CounterState where
  act := fun _ state => state
  act_id := by intro state; rfl
  act_comp := by intro χ ψ state; rfl
  act_inv := by intro χ state; rfl

/-- The swap is genuinely non-identity on the used finite name carrier. -/
theorem twoCounterSwap_moves : twoCounterSwap 0 ≠ (0 : Fin 2) := by
  decide

/-- The name-bearing trace metadata for the P7 regression. -/
def twoCounterAlphaTrace : NameTrace (Fin 2) :=
  { initialIssued := ({0} : Finset (Fin 2))
    allocations := [1]
    parents := [none]
    references := [some 1]
    boundarySnapshots := [({0, 1} : Finset (Fin 2))]
    support := ({0, 1} : Finset (Fin 2)) }

/-- The P7 alpha trace has a covering support envelope. -/
theorem twoCounterAlphaTraceSupport : TraceSupport twoCounterAlphaTrace := by
  constructor <;> decide

/-- The P7 alpha trace does not reuse its allocated name. -/
theorem twoCounterAlphaTraceNoReuse : TraceNoReuse twoCounterAlphaTrace := by
  constructor <;> decide

/-- The trace transport changes every used name-bearing field under the swap. -/
def twoCounterAlphaTraceCheck : Bool :=
  decide ((renameNameTrace twoCounterSwap twoCounterAlphaTrace).initialIssued =
      ({1} : Finset (Fin 2)) ∧
    (renameNameTrace twoCounterSwap twoCounterAlphaTrace).allocations = [0] ∧
    (renameNameTrace twoCounterSwap twoCounterAlphaTrace).parents = [none] ∧
    (renameNameTrace twoCounterSwap twoCounterAlphaTrace).references = [some 0] ∧
    (renameNameTrace twoCounterSwap twoCounterAlphaTrace).boundarySnapshots =
      [({0, 1} : Finset (Fin 2))] ∧
    (renameNameTrace twoCounterSwap twoCounterAlphaTrace).support =
      ({0, 1} : Finset (Fin 2)))

/-- The P6 execution transport theorem applies to the P7 success iterator under the swap. -/
theorem twoCounterAlphaExec_transport :
    exec (renameIterator twoCounterAlphaAction twoCounterSwap twoCounterIterator)
        (twoCounterAlphaAction.act twoCounterSwap twoCounterS0) =
      renameExec twoCounterAlphaAction twoCounterSwap
        (exec twoCounterIterator twoCounterS0) := by
  exact exec_rename_transport twoCounterAlphaAction twoCounterSwap twoCounterIterator twoCounterS0

/-- The P6 execution transport theorem also applies to the P7 failure iterator. -/
theorem twoCounterAlphaFailureExec_transport :
    exec (renameIterator twoCounterAlphaAction twoCounterSwap twoCounterFailureIterator)
        (twoCounterAlphaAction.act twoCounterSwap twoCounterS0) =
      renameExec twoCounterAlphaAction twoCounterSwap
        (exec twoCounterFailureIterator twoCounterS0) := by
  exact exec_rename_transport twoCounterAlphaAction twoCounterSwap
    twoCounterFailureIterator twoCounterS0

/-- The transported successful execution retains its success constructor and final state. -/
theorem twoCounterAlphaSuccess_transport :
    renameExec twoCounterAlphaAction twoCounterSwap
        (.success { state := (1, 1), undo := fun value => (value.1 - 1, value.2 - 1) } :
          ExecResult CounterState Unit) =
      .success { state := (1, 1), undo := fun value => (value.1 - 1, value.2 - 1) } := by
  rfl

/-- The transported failure payload retains its error, boundary, and prefix inverse. -/
theorem twoCounterAlphaFailure_transport :
    renameExec twoCounterAlphaAction twoCounterSwap
        (.failure { error := (), boundary := (1, 0), prefixUndo := (inc1 twoCounterS0).undo } :
          ExecResult CounterState Unit) =
      .failure { error := (), boundary := (1, 0), prefixUndo := (inc1 twoCounterS0).undo } := by
  rfl

/-- A boundary with the same core state but renamed trace metadata. -/
def twoCounterAlphaBoundary : AlphaBoundary (Fin 2) CounterState :=
  { state := twoCounterS0, trace := twoCounterAlphaTrace }

/-- The name-aware boundary after applying the finite swap to the trace. -/
def twoCounterAlphaBoundaryRenamed : AlphaBoundary (Fin 2) CounterState :=
  { state := twoCounterS0, trace := renameNameTrace twoCounterSwap twoCounterAlphaTrace }

/-- Core observation ignores the alpha-labelled trace metadata. -/
theorem twoCounterAlphaCoreObs_ignores :
    (coreBoundaryObs (equality CounterState)).rel
      twoCounterAlphaBoundary twoCounterAlphaBoundaryRenamed :=
  coreBoundaryObs_ignores_trace (equality CounterState) rfl

/-- Name-aware observation distinguishes the two alpha-labelled boundaries. -/
theorem twoCounterAlphaNameAware_distinguishes :
    ¬ (nameAwareBoundaryObs (equality CounterState)).rel
      twoCounterAlphaBoundary twoCounterAlphaBoundaryRenamed := by
  apply nameAwareBoundaryObs_distinguishes (equality CounterState)
  · rfl
  · intro h
    have halloc := congrArg (fun trace => trace.allocations)
      (show twoCounterAlphaTrace = renameNameTrace twoCounterSwap twoCounterAlphaTrace from h)
    simp [twoCounterAlphaTrace, renameNameTrace, renameParentRef, twoCounterSwap] at halloc

end AlphaRegression

/-! ### The executable slice report -/

section Report

/-- The final state of the success trace from `(0, 7)`. -/
def successFinal : CounterState :=
  match execFrom counterIterator .start s0 with
  | .success r => r.state
  | .failure _ => (999, 999)

/-- The recovered state of the success trace. -/
def successRecovered : CounterState :=
  match execFrom counterIterator .start s0 with
  | .success r => r.undo r.state
  | .failure _ => (999, 999)

/-- The failing trace retains error, boundary, and the recovering prefix inverse. -/
def failureBoundary : Bool :=
  match execFrom failingIterator .start (0, 0) with
  | .failure f =>
      decide (f.error = () ∧ f.boundary = (1, 0) ∧ f.prefixUndo f.boundary = (0, 0))
  | .success _ => false

/-- The success trace ends at `(5, 7)`. -/
theorem successFinal_eq : successFinal = (5, 7) := by
  unfold successFinal
  rw [counterExec_eq]

/-- The composed LIFO inverse recovers `(0, 7)`. -/
theorem successRecovered_eq : successRecovered = (0, 7) := by
  unfold successRecovered
  rw [counterExec_eq]
  rfl

/-- The failing trace passes the boundary/prefix check. -/
theorem failureBoundary_eq : failureBoundary = true := by
  unfold failureBoundary
  rw [failingExec_eq]
  rfl

/-- The final state of the canonical P7 two-counter success trace. -/
def twoCounterSuccessFinal : CounterState :=
  match execFrom twoCounterIterator .start twoCounterS0 with
  | .success result => result.state
  | .failure _ => (999, 999)

/-- The recovered state of the canonical P7 two-counter success trace. -/
def twoCounterSuccessRecovered : CounterState :=
  match execFrom twoCounterIterator .start twoCounterS0 with
  | .success result => result.undo result.state
  | .failure _ => (999, 999)

/-- The final state of the P7 success path is `(1, 1)`. -/
theorem twoCounterSuccessFinal_eq : twoCounterSuccessFinal = (1, 1) := by
  unfold twoCounterSuccessFinal
  rw [twoCounterSuccessExec_eq]

/-- The selected LIFO inverse of the P7 success path recovers `(0, 0)`. -/
theorem twoCounterSuccessRecovered_eq : twoCounterSuccessRecovered = (0, 0) := by
  unfold twoCounterSuccessRecovered
  rw [twoCounterSuccessExec_eq]
  rfl

/-- The P7 failure trace retains its error, boundary, and prefix undo. -/
def twoCounterFailureBoundary : Bool :=
  match execFrom twoCounterFailureIterator .start twoCounterS0 with
  | .failure failure =>
      decide (failure.error = () ∧ failure.boundary = (1, 0) ∧
        failure.prefixUndo failure.boundary = twoCounterS0)
  | .success _ => false

/-- The P7 failure trace passes the complete boundary/prefix check. -/
theorem twoCounterFailureBoundary_eq : twoCounterFailureBoundary = true := by
  unfold twoCounterFailureBoundary
  rw [twoCounterFailureExec_eq]
  rfl

/-- The P7 success inverse and the two independent increments agree at the canonical input. -/
def twoCounterSuccessInverseCheck : Bool :=
  decide ((fun value : CounterState => (value.1 - 1, value.2 - 1)) (1, 1) = twoCounterS0)

/-- The two increments commute on the canonical finite state. -/
def twoCounterIndependenceCheck : Bool :=
  decide ((seqRun inc1 inc2 twoCounterS0).state = (seqRun inc2 inc1 twoCounterS0).state)

/-- The explicit foreign-stability counterexample is a true finite mismatch. -/
def twoCounterForeignStabilityCheck : Bool :=
  STC.Examples.TwoCounter.foreignStabilityCounterexample

/-- The rank certificates and alpha-labelled trace checks are executable booleans. -/
def twoCounterRankCheck : Bool :=
  decide (twoCounterRank .afterInc1 < twoCounterRank .start ∧
    twoCounterRank .afterInc2 < twoCounterRank .afterInc1 ∧
    twoCounterFailureRank .check < twoCounterFailureRank .start)

def twoCounterAlphaSwapCheck : Bool := decide (twoCounterSwap 0 ≠ (0 : Fin 2))

def twoCounterAlphaTraceSupportCheck : Bool :=
  decide ((0 : Fin 2) ∈ twoCounterAlphaTrace.support ∧
    (1 : Fin 2) ∈ twoCounterAlphaTrace.support)

def twoCounterAlphaTraceNoReuseCheck : Bool :=
  decide ((1 : Fin 2) ∉ twoCounterAlphaTrace.initialIssued)

def twoCounterAlphaCoreCheck : Bool :=
  decide (twoCounterAlphaBoundary.state = twoCounterAlphaBoundaryRenamed.state)

def twoCounterAlphaNameAwareCheck : Bool :=
  decide (twoCounterAlphaTrace.allocations ≠
    (renameNameTrace twoCounterSwap twoCounterAlphaTrace).allocations)

/-- The mixed-tag stage pair is rejected by the tagged stage relation. -/
theorem stageMixed_not_rel :
    ¬ StageRelC (equality CounterState) (equality Unit).rel
      ((.halt { state := (0, 7), undo := id } : StageResult CounterState Unit Control))
      ((.raise () : StageResult CounterState Unit Control)) := by
  intro h
  cases h

/-- The executable mixed-tag check: a direct constructor-tag computation on the
concrete stage pair, mirroring `stageMixed_not_rel`. -/
def stageMixedRejected : Bool :=
  match (.halt { state := (0, 7), undo := id } : StageResult CounterState Unit Control),
      (.raise () : StageResult CounterState Unit Control) with
  | .halt _, .halt _ => false
  | .yield _ _, .yield _ _ => false
  | .raise _, .raise _ => false
  | _, _ => true

/-- The equality specialization of the execution relation is reflexive on a concrete
successful execution. -/
theorem execSuccess_refl :
    (execRelSpec (equality CounterState) (equality Unit)).rel
      (.success { state := (1, 0), undo := id })
      (.success { state := (1, 0), undo := id }) :=
  (execRelSpec (equality CounterState) (equality Unit)).refl _

/-- The executable reflexivity check: a direct constructor-tag and state computation
on the concrete execution pair, mirroring `execSuccess_refl`. -/
def execReflCheck : Bool :=
  match (.success { state := (1, 0), undo := id } : ExecResult CounterState Unit),
      (.success { state := (1, 0), undo := id } : ExecResult CounterState Unit) with
  | .success left, .success right => decide (left.state = right.state)
  | .failure _, .failure _ => false
  | _, _ => false

/-- The aggregated executable slice report. -/
structure SliceReport where
  successFinal : CounterState
  successRecovered : CounterState
  stageCount : Nat
  failureBoundary : Bool
  stageMixedRejected : Bool
  execRefl : Bool
  twoCounterSuccessFinal : CounterState
  twoCounterSuccessRecovered : CounterState
  twoCounterStageCount : Nat
  twoCounterFailureBoundary : Bool
  twoCounterFailureStageCount : Nat
  twoCounterSuccessInverse : Bool
  independence : Bool
  foreignStabilityCounterexample : Bool
  rankChecks : Bool
  alphaSwapMoves : Bool
  alphaTraceSupport : Bool
  alphaTraceNoReuse : Bool
  alphaCoreObservation : Bool
  alphaNameAwareObservation : Bool
deriving DecidableEq, Repr

/-- The computed slice report. -/
def sliceReport : SliceReport :=
  { successFinal := successFinal
    successRecovered := successRecovered
    stageCount := stageCountFrom counterIterator .start (0, 7)
    failureBoundary := failureBoundary
    stageMixedRejected := stageMixedRejected
    execRefl := execReflCheck
    twoCounterSuccessFinal := twoCounterSuccessFinal
    twoCounterSuccessRecovered := twoCounterSuccessRecovered
    twoCounterStageCount := stageCountFrom twoCounterIterator .start twoCounterS0
    twoCounterFailureBoundary := twoCounterFailureBoundary
    twoCounterFailureStageCount := stageCountFrom twoCounterFailureIterator .start twoCounterS0
    twoCounterSuccessInverse := twoCounterSuccessInverseCheck
    independence := twoCounterIndependenceCheck
    foreignStabilityCounterexample := twoCounterForeignStabilityCheck
    rankChecks := twoCounterRankCheck
    alphaSwapMoves := twoCounterAlphaSwapCheck
    alphaTraceSupport := twoCounterAlphaTraceSupportCheck
    alphaTraceNoReuse := twoCounterAlphaTraceNoReuseCheck
    alphaCoreObservation := twoCounterAlphaCoreCheck
    alphaNameAwareObservation := twoCounterAlphaNameAwareCheck }

-- No top-level `#eval` (library modules must not evaluate exposed declarations on
-- Windows); the pinned `example` below elaborates the expected report.

/-- The expected slice report, pinned by the equation-based trace proofs. -/
example : sliceReport =
    { successFinal := (5, 7)
      successRecovered := (0, 7)
      stageCount := 5
      failureBoundary := true
      stageMixedRejected := true
      execRefl := true
      twoCounterSuccessFinal := (1, 1)
      twoCounterSuccessRecovered := (0, 0)
      twoCounterStageCount := 3
      twoCounterFailureBoundary := true
      twoCounterFailureStageCount := 2
      twoCounterSuccessInverse := true
      independence := true
      foreignStabilityCounterexample := true
      rankChecks := true
      alphaSwapMoves := true
      alphaTraceSupport := true
      alphaTraceNoReuse := true
      alphaCoreObservation := true
      alphaNameAwareObservation := true } := by
  unfold sliceReport
  rw [successFinal_eq, successRecovered_eq, failureBoundary_eq, stageCount_eq,
    twoCounterSuccessFinal_eq, twoCounterSuccessRecovered_eq,
    twoCounterFailureBoundary_eq, twoCounterSuccessStageCount_eq,
    twoCounterFailureStageCount_eq]
  decide

end Report

end

end STC.Examples.VerticalSlice
