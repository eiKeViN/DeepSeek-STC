module

public import STC.Alpha.Transport

/-!
# The finite alpha-transport fixture

The P6-T04 finite evidence over `N := Fin 2` with the swap permutation: a small state
carrying a name plus a reversible bit, the swap action instance, a nontrivial
`renameUndo`/result check, a two-stage ranked iterator whose renamed execution agrees
with `renameExec` (success and failure, pinned through the execution equations), the
freshness/ledger and no-reuse transport checks, and the core-versus-name-aware
observation split.  This fixture is evidence for the selected finite profile only.

## Main declarations

* `AlphaState`, `alphaSwap`, `alphaAction`: the finite swap action instance;
* `alphaStep`, `flipUndo`, `alphaRun`, `alphaRank`, `alphaIterator`, `failingRun`,
  `failingIterator`: the two-stage machines;
* `alphaStageWitness`, `alphaExec_step`, `alphaExec_root`, `alphaExecTransport_eq`,
  `alphaFailing_exec`, `alphaFailureTransport_eq`: the execution evidence;
* `alphaTrace`, `alphaTraceSupport`, `alphaTraceNoReuse` and their rename transports;
* `alphaBoundaryExample`, `alphaCoreObs_ignores`, `alphaNameAware_distinguishes`;
* `AlphaReport`, `alphaReport`: the pinned executable report.
-/

namespace STC.Examples.Alpha

@[expose] public section

/-! ### The finite swap action -/

section SwapAction

/-- The fixture state: one name from `Fin 2` plus a reversible bit. -/
abbrev AlphaState := Fin 2 × Bool

/-- The nontrivial finite permutation: the swap on `Fin 2`. -/
def alphaSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- The name action: rename the name component; the bit is name-neutral. -/
def alphaAct (χ : Equiv.Perm (Fin 2)) (s : AlphaState) : AlphaState :=
  (χ s.1, s.2)

/-- The finite swap action instance with the checked ADR-06 laws. -/
def alphaAction : AlphaAction (Fin 2) AlphaState where
  act := alphaAct
  act_id := by
    intro s
    cases s
    simp [alphaAct]
  act_comp := by
    intro χ ψ s
    cases s
    simp [alphaAct]
  act_inv := by
    intro χ s
    cases s
    simp [alphaAct]

/-- The identity action leaves the state unchanged. -/
theorem alphaAct_refl :
    alphaAction.act (Equiv.refl (Fin 2)) (0, true) = (0, true) := by
  decide

/-- The swap action moves the name; the bit is unchanged. -/
theorem alphaAct_swap :
    alphaAction.act alphaSwap (0, true) = (1, true) := by
  decide

/-- The inverse action undoes the swap, by the checked inverse law. -/
theorem alphaAct_inv_check :
    alphaAction.act alphaSwap.symm (alphaAction.act alphaSwap (0, true)) = (0, true) := by
  simpa using alphaAction.act_inv alphaSwap (0, true)

/-- The swap action is genuinely nontrivial. -/
theorem alphaAct_swap_moves :
    alphaAction.act alphaSwap (0, true) ≠ (0, true) := by
  decide

/-- The equality specialization is alpha-invariant for the fixture action. -/
theorem alphaAction_invariant_eq :
    AlphaInvariant alphaAction (fun x y => x = y) :=
  alphaInvariant_eq alphaAction

/-- Flip the reversible bit; the inverse is the flip itself. -/
def alphaStep (s : AlphaState) : AlphaState :=
  (s.1, !s.2)

/-- `alphaStep` is an involution: the bit flips back. -/
theorem alphaStep_involutive : ∀ s, alphaStep (alphaStep s) = s := by
  intro s
  cases s
  simp [alphaStep]

/-- A nontrivial selected inverse over the fixture state. -/
def flipUndo (s : AlphaState) : AlphaState :=
  (s.1, !s.2)

/-- The conjugated `renameUndo` at the swap: the name and the bit both flip once. -/
theorem renameUndo_swap_check :
    renameUndo alphaAction alphaSwap flipUndo (1, true) = (1, false) := by
  decide

/-- The renamed effect result rewrites the state by the action and the inverse by
conjugation. -/
theorem renameEffectResult_swap_check :
    renameEffectResult alphaAction alphaSwap { state := (0, true), undo := flipUndo } =
      { state := (1, true), undo := renameUndo alphaAction alphaSwap flipUndo } := by
  rfl

end SwapAction

/-! ### The two-stage machines -/

section Machine

/-- The two-stage control carrier. -/
inductive AlphaCode where
  | root
  | step
deriving DecidableEq, Repr

/-- The rank certificate: the root stage ranks above the final stage. -/
def alphaRank : AlphaCode → Nat
  | .root => 1
  | .step => 0

/-- One stage result: flip the bit and select the flip as the inverse. -/
def alphaStepResult (s : AlphaState) : EffectResult AlphaState :=
  { state := alphaStep s, undo := alphaStep }

/-- The success machine: the root yields into the final stage, both flipping the bit. -/
def alphaRun : AlphaCode → AlphaState → StageResult AlphaState Bool AlphaCode
  | .root, s => .yield (alphaStepResult s) .step
  | .step, s => .halt (alphaStepResult s)

/-- The strict-successor certificate of the success machine. -/
theorem alphaNextLt : ∀ {q s result q'}, alphaRun q s = .yield result q' →
    alphaRank q' < alphaRank q := by
  intro q s result q' h
  cases q with
  | root =>
      simp only [alphaRun, alphaRank] at h ⊢
      cases h
      decide
  | step => simp [alphaRun] at h

/-- The success iterator. -/
def alphaIterator : RankedIterator AlphaState Bool AlphaCode where
  root := .root
  rank := alphaRank
  run := alphaRun
  next_lt := alphaNextLt

/-- The failing machine: the root raises immediately. -/
def failingRun : AlphaCode → AlphaState → StageResult AlphaState Bool AlphaCode
  | .root, _ => .raise true
  | .step, s => .halt (alphaStepResult s)

/-- The strict-successor certificate of the failing machine: no stage yields. -/
theorem failingNextLt : ∀ {q s result q'}, failingRun q s = .yield result q' →
    alphaRank q' < alphaRank q := by
  intro q s result q' h
  cases q with
  | root => simp [failingRun] at h
  | step => simp [failingRun] at h

/-- The failing iterator. -/
def failingIterator : RankedIterator AlphaState Bool AlphaCode where
  root := .root
  rank := alphaRank
  run := failingRun
  next_lt := failingNextLt

/-- Every stage of the success machine recovers locally and selects only
relation-preserving inverses: the fixture stage witness. -/
theorem alphaStageWitness : StageWitness (equality AlphaState) alphaIterator := by
  constructor
  intro q input
  cases q with
  | root =>
      simp only [alphaIterator, alphaRun, alphaStepResult, alphaStep, equality]
      constructor
      · exact alphaStep_involutive input
      · intro x y h
        cases h
        rfl
  | step =>
      simp only [alphaIterator, alphaRun, alphaStepResult, alphaStep, equality]
      constructor
      · exact alphaStep_involutive input
      · intro x y h
        cases h
        rfl

end Machine

/-! ### The computed execution traces -/

section Traces

/-- The final stage halts and returns its flip. -/
theorem alphaExec_step (s : AlphaState) :
    execFrom alphaIterator AlphaCode.step s = .success (alphaStepResult s) := by
  rw [execFrom_halt (it := alphaIterator)
    (h := (show alphaIterator.run AlphaCode.step s = .halt (alphaStepResult s) from rfl))]

/-- The full success trace from the root: two flips compose the inverse in the
outer-after-inner order, and the bit returns. -/
theorem alphaExec_root :
    execFrom alphaIterator AlphaCode.root (0, true) =
      .success { state := (0, true), undo := alphaStep ∘ alphaStep } := by
  rw [execFrom_yield_success (it := alphaIterator)
    (hyield := (show alphaIterator.run AlphaCode.root (0, true) =
      .yield (alphaStepResult (0, true)) AlphaCode.step from rfl))
    (hinner := alphaExec_step (alphaStepResult (0, true)).state)]
  simp only [alphaStepResult, alphaStep]
  rfl

/-- The expected renamed success value of the fixture trace. -/
def alphaRenameExpected : ExecResult AlphaState Bool :=
  .success { state := (1, true), undo := renameUndo alphaAction alphaSwap (alphaStep ∘ alphaStep) }

/-- The renamed execution of the fixture iterator agrees with `renameExec` on the
finite pinned value: one successful result, both name and undo transported. -/
theorem alphaExecTransport_eq :
    execFrom (renameIterator alphaAction alphaSwap alphaIterator) AlphaCode.root (1, true) =
      alphaRenameExpected := by
  have htransport :=
    execFrom_rename_transport alphaAction alphaSwap alphaIterator AlphaCode.root (0, true)
  rw [alphaExec_root] at htransport
  simpa [alphaRenameExpected, alphaAction, alphaAct, alphaSwap, renameExec, renameEffectResult]
    using htransport

/-- The generic execution transport theorem at the fixture instance. -/
theorem alphaExecTransport_theorem :
    execFrom (renameIterator alphaAction alphaSwap alphaIterator) AlphaCode.root
        (alphaAction.act alphaSwap (0, true)) =
      renameExec (E := Bool) alphaAction alphaSwap
        (execFrom alphaIterator AlphaCode.root (0, true)) :=
  execFrom_rename_transport alphaAction alphaSwap alphaIterator AlphaCode.root (0, true)

/-- The failing trace raises at the root boundary with the identity prefix undo. -/
theorem alphaFailing_exec :
    execFrom failingIterator AlphaCode.root (0, true) =
      .failure { error := true, boundary := (0, true), prefixUndo := id } := by
  rw [execFrom_raise (it := failingIterator)
    (h := (show failingIterator.run AlphaCode.root (0, true) = .raise true from rfl))]

/-- The renamed failing execution retains the failure tag, the neutral error, the
identity prefix undo, and transports the boundary state. -/
theorem alphaFailureTransport_eq :
    execFrom (renameIterator alphaAction alphaSwap failingIterator) AlphaCode.root (1, true) =
      .failure { error := true, boundary := (1, true), prefixUndo := id } := by
  have htransport :=
    execFrom_rename_transport alphaAction alphaSwap failingIterator AlphaCode.root (0, true)
  rw [alphaFailing_exec] at htransport
  simpa [alphaAction, alphaAct, alphaSwap, renameExec, renameFailure, renameUndo_id_fn] using
    htransport

end Traces

/-! ### Freshness, ledger, and trace checks -/

section Freshness

/-- The fixture parent-permission predicate: every parent is allowed. -/
def parentAllowedAll (_current : Finset (Fin 2)) (_parent : ParentRef (Fin 2)) : Prop :=
  True

instance : ∀ current parent, Decidable (parentAllowedAll current parent) := by
  intro current parent
  change Decidable True
  infer_instance

/-- The initial ledger: only the name `0` has ever been issued. -/
def alphaLedger : NameLedger (Fin 2) :=
  { everIssued := ({0} : Finset (Fin 2)) }

/-- Allocating the fresh name `1` from the empty current set succeeds, updates both
sets, keeps the ledger sound, and issues `1`; the old name `0` stays issued. -/
def alphaAllocateCheck : Bool :=
  match allocate? parentAllowedAll (∅ : Finset (Fin 2)) alphaLedger none 1 with
  | some (current', ledger') =>
      decide (current' = insert 1 (∅ : Finset (Fin 2)) ∧
        ledger'.everIssued = insert 1 ({0} : Finset (Fin 2)) ∧
        (∀ n : Fin 2, n ∈ current' → n ∈ ledger'.everIssued) ∧
        (0 : Fin 2) ∈ ledger'.everIssued ∧ (1 : Fin 2) ∈ ledger'.everIssued)
  | none => false

/-- Renaming `{1}` by the swap moves the fresh name: the renamed `1` is present and
`1` itself is fresh in the renamed set. -/
def alphaFreshnessCheck : Bool :=
  decide ((alphaSwap 1) ∈ renameFinset alphaSwap ({1} : Finset (Fin 2)) ∧
    (1 : Fin 2) ∉ renameFinset alphaSwap ({1} : Finset (Fin 2)))

/-- The freshness transport theorem at the fixture instance. -/
theorem alphaFreshness_transport :
    CurrentFresh (renameFinset alphaSwap ({1} : Finset (Fin 2))) (alphaSwap 1) ↔
      CurrentFresh ({1} : Finset (Fin 2)) 1 :=
  currentFresh_rename alphaSwap

/-- The fixture trace: `0` initially issued, `1` allocated under the synthetic root. -/
def alphaTrace : NameTrace (Fin 2) :=
  { initialIssued := ({0} : Finset (Fin 2))
    allocations := [1]
    parents := [none]
    references := [none]
    boundarySnapshots := [({0} : Finset (Fin 2))]
    support := ({0, 1} : Finset (Fin 2)) }

/-- The fixture trace declares a covering support envelope. -/
theorem alphaTraceSupport : TraceSupport alphaTrace := by
  constructor <;> decide

/-- The fixture trace satisfies no-reuse: one allocation, fresh relative to the
initial issued set. -/
theorem alphaTraceNoReuse : TraceNoReuse alphaTrace := by
  constructor <;> decide

/-- The support envelope transports through the swap renaming. -/
theorem alphaTraceSupport_rename :
    TraceSupport (renameNameTrace alphaSwap alphaTrace) :=
  traceSupport_rename alphaSwap alphaTraceSupport

/-- No-reuse transports through the swap renaming. -/
theorem alphaTraceNoReuse_rename :
    TraceNoReuse (renameNameTrace alphaSwap alphaTrace) :=
  traceNoReuse_rename alphaSwap alphaTraceNoReuse

/-- The swapped trace has the mirrored initial set, allocation, and support. -/
def alphaTraceRenameCheck : Bool :=
  decide ((renameNameTrace alphaSwap alphaTrace).initialIssued = ({1} : Finset (Fin 2)) ∧
    (renameNameTrace alphaSwap alphaTrace).allocations = [0] ∧
    (renameNameTrace alphaSwap alphaTrace).parents = [none] ∧
    (renameNameTrace alphaSwap alphaTrace).references = [none] ∧
    (renameNameTrace alphaSwap alphaTrace).boundarySnapshots = [({1} : Finset (Fin 2))] ∧
    (renameNameTrace alphaSwap alphaTrace).support = ({0, 1} : Finset (Fin 2)))

end Freshness

/-! ### The core versus name-aware observation split -/

section Observations

/-- A boundary carrying the fixture state and trace. -/
def alphaBoundaryExample : AlphaBoundary (Fin 2) AlphaState :=
  { state := (0, true), trace := alphaTrace }

/-- The same state with the swapped trace metadata. -/
def alphaBoundaryRenamed : AlphaBoundary (Fin 2) AlphaState :=
  { state := (0, true), trace := renameNameTrace alphaSwap alphaTrace }

/-- The core observation ignores the trace metadata and relates the two boundaries. -/
theorem alphaCoreObs_ignores :
    (coreBoundaryObs (equality AlphaState)).rel alphaBoundaryExample alphaBoundaryRenamed :=
  coreBoundaryObs_ignores_trace (equality AlphaState) rfl

/-- The explicitly name-aware observation distinguishes the two boundaries: their
traces differ in the initial issued set. -/
theorem alphaNameAware_distinguishes :
    ¬ (nameAwareBoundaryObs (equality AlphaState)).rel alphaBoundaryExample alphaBoundaryRenamed := by
  apply nameAwareBoundaryObs_distinguishes
  · rfl
  · intro h
    have hinit := congrArg NameTrace.initialIssued h
    have hinit' : alphaTrace.initialIssued = (renameNameTrace alphaSwap alphaTrace).initialIssued := by
      simpa [alphaBoundaryExample, alphaBoundaryRenamed] using hinit
    have hmem : (0 : Fin 2) ∈ alphaTrace.initialIssued := by
      simp [alphaTrace]
    have hback : (0 : Fin 2) ∉ (renameNameTrace alphaSwap alphaTrace).initialIssued := by
      decide
    rw [hinit'] at hmem
    exact hback hmem

/-- The executable value of the core observation on the pair. -/
def alphaCoreObsCheck : Bool :=
  decide (alphaBoundaryExample.state = alphaBoundaryRenamed.state)

/-- The executable value of the name-aware distinction: the initial issued sets
differ. -/
def alphaNameObsCheck : Bool :=
  decide (alphaBoundaryExample.trace.initialIssued ≠ alphaBoundaryRenamed.trace.initialIssued)

end Observations

/-! ### The pinned executable report -/

section Report

/-- The aggregated executable alpha-transport report.  The execution-transport rows
are not `decide`-computable (the well-founded `execFrom` carries no `DecidableEq` and
cannot be kernel-reduced); they are pinned separately by `alphaExecTransport_eq` and
`alphaFailureTransport_eq` through the execution equation theorems, as P4 does. -/
structure AlphaReport where
  actionSwap : Bool
  actionInv : Bool
  renameUndoValue : Bool
  allocate : Bool
  freshness : Bool
  traceRename : Bool
  coreObs : Bool
  nameObs : Bool
deriving DecidableEq, Repr

/-- The computed alpha-transport report. -/
def alphaReport : AlphaReport :=
  { actionSwap := decide (alphaAction.act alphaSwap (0, true) = (1, true))
    actionInv := decide
      (alphaAction.act alphaSwap.symm (alphaAction.act alphaSwap (0, true)) = (0, true))
    renameUndoValue := decide (renameUndo alphaAction alphaSwap flipUndo (1, true) = (1, false))
    allocate := alphaAllocateCheck
    freshness := alphaFreshnessCheck
    traceRename := alphaTraceRenameCheck
    coreObs := alphaCoreObsCheck
    nameObs := alphaNameObsCheck }

-- No top-level `#eval` (library modules must not evaluate exposed declarations on
-- Windows); the pinned `example` below elaborates the expected report.

/-- The expected alpha-transport report, pinned by an executable check. -/
example : alphaReport =
    { actionSwap := true
      actionInv := true
      renameUndoValue := true
      allocate := true
      freshness := true
      traceRename := true
      coreObs := true
      nameObs := true } := by
  decide

end Report

end

end STC.Examples.Alpha
