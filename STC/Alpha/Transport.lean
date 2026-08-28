module

public import STC.Alpha.Core
public import STC.Alpha.Trace

/-!
# Alpha transport over the ranked iterator

The P6-T02 name-neutral transport layer: the renamed ranked iterator over the ADR-06
action convention, the stage/simulation/bisimulation transports under `AlphaInvariant`,
the ADR-06 inverse-properness and witness packages, and the well-founded
`execFrom`/`exec` transport equations.  This file imports `STC.Alpha.Trace`, which is
the deliberate P6-T03 boundary split and is imported only from here.

In this profile `E` and `Q` are name-neutral and deliberately unchanged; a
named-payload profile must supply its own payload actions and interpreter laws.

## Main declarations

* `renameIterator`: the renamed ranked iterator with preserved `root` and `rank`;
* `renameIterator_run_input`, `renameIterator_run_transport`: the run equations;
* `stageRelC_rename`, `iteratorSimulation_rename`, `iteratorBisim_rename`;
* `StageInverseProper`, `IteratorInverseProper`: the ADR-06 inverse-properness packages;
* `stageInverseProper_rename`, `iteratorInverseProper_rename`, `stageWitness_rename`,
  `iteratorWitness_rename`;
* `execFrom_rename_transport`, `exec`, `exec_rename_transport`: the execution transport;
* `ExecTransportContract`, `execTransportContract_proof`: the explicit boundary contract.
-/

universe u v

namespace STC

@[expose] public section

variable {N : Type u} {S E Q : Type v}

/-! ### The renamed ranked iterator -/

section IteratorRenaming

/-- Rename a ranked iterator: `root` and `rank` are preserved, and each run stage is
the renamed stage of the original iterator on the inverse-renamed input.  The
strict-successor certificate is transported by the existing `it.next_lt`; no new fuel,
coinduction, or rank adjustment is introduced. -/
def renameIterator (A : AlphaAction N S) (χ : Equiv.Perm N)
    (it : RankedIterator S E Q) : RankedIterator S E Q where
  root := it.root
  rank := it.rank
  run := fun q s => renameStage A χ (it.run q (A.act χ.symm s))
  next_lt := by
    intro q s result q' h
    cases hrun : it.run q (A.act χ.symm s) with
    | halt r => simp [renameStage, hrun] at h
    | raise e => simp [renameStage, hrun] at h
    | yield r next =>
        simp [renameStage, hrun] at h
        rcases h with ⟨hr, hnext⟩
        subst q'
        exact it.next_lt hrun

/-- Renaming preserves the root control code. -/
theorem renameIterator_root (A : AlphaAction N S) (χ : Equiv.Perm N)
    (it : RankedIterator S E Q) :
    (renameIterator A χ it).root = it.root := rfl

/-- Renaming preserves the rank certificate. -/
theorem renameIterator_rank (A : AlphaAction N S) (χ : Equiv.Perm N)
    (it : RankedIterator S E Q) :
    (renameIterator A χ it).rank = it.rank := rfl

/-- The run equation on the inverse-renamed input side. -/
theorem renameIterator_run_input (A : AlphaAction N S) (χ : Equiv.Perm N)
    (it : RankedIterator S E Q) (q : Q) (s : S) :
    (renameIterator A χ it).run q s = renameStage A χ (it.run q (A.act χ.symm s)) := rfl

/-- The run equation on the renamed input side: running the renamed iterator on the
acted input is the renamed stage of the original run. -/
theorem renameIterator_run_transport (A : AlphaAction N S) (χ : Equiv.Perm N)
    (it : RankedIterator S E Q) (q : Q) (s : S) :
    (renameIterator A χ it).run q (A.act χ s) = renameStage A χ (it.run q s) := by
  simp [renameIterator, A.act_inv]

end IteratorRenaming

/-! ### Stage, simulation, and bisimulation transport -/

section RelationTransport

/-- `StageRelC` transports through the renamed stage whenever the state relation is
alpha-invariant; the unchanged neutral error and continuation pass through. -/
theorem stageRelC_rename (A : AlphaAction N S) (R : RelSpec S) (T : RelSpec E)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    {left right : StageResult S E Q} (h : StageRelC R T.rel left right) :
    StageRelC R T.rel (renameStage A χ left) (renameStage A χ right) := by
  cases left with
  | halt l =>
      cases right with
      | halt r =>
          have hl : EffectResultRel R l r := by simpa [StageRelC] using h
          simp only [StageRelC, EffectResultRel, renameStage, renameEffectResult]
          exact ⟨(hinv χ _ _).1 hl.1, pointwise_renameUndo A R hinv χ hl.2⟩
      | yield r next => simp [StageRelC] at h
      | raise e => simp [StageRelC] at h
  | yield l next =>
      cases right with
      | halt r => simp [StageRelC] at h
      | yield r next' =>
          have hl : EffectResultRel R l r ∧ next = next' := by simpa [StageRelC] using h
          simp only [StageRelC, EffectResultRel, renameStage, renameEffectResult]
          exact ⟨⟨(hinv χ _ _).1 hl.1.1, pointwise_renameUndo A R hinv χ hl.1.2⟩, hl.2⟩
      | raise e => simp [StageRelC] at h
  | raise e =>
      cases right with
      | halt r => simp [StageRelC] at h
      | yield r next => simp [StageRelC] at h
      | raise e' => simpa [StageRelC, renameStage] using h

/-- `IteratorSimulation` transports through iterator renaming under `AlphaInvariant`. -/
theorem iteratorSimulation_rename (A : AlphaAction N S) (R : RelSpec S) (T : RelSpec E)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    (left right : RankedIterator S E Q) (hsim : IteratorSimulation R T left right) :
    IteratorSimulation R T (renameIterator A χ left) (renameIterator A χ right) := by
  constructor
  intro q s t hst
  have hst' : R.rel (A.act χ.symm s) (A.act χ.symm t) :=
    (hinv χ.symm s t).1 hst
  have hs := hsim.run_related q (A.act χ.symm s) (A.act χ.symm t) hst'
  change StageRelC R T.rel
    (renameStage A χ (left.run q (A.act χ.symm s)))
    (renameStage A χ (right.run q (A.act χ.symm t)))
  exact stageRelC_rename A R T hinv χ hs

/-- `IteratorBisim` transports through iterator renaming under `AlphaInvariant`.  The
production bisimulation carries no separate continuation relation; both directions use
the same `R` and `T`, so nothing besides the state relation needs a converse. -/
theorem iteratorBisim_rename (A : AlphaAction N S) (R : RelSpec S) (T : RelSpec E)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    (left right : RankedIterator S E Q) (hbis : IteratorBisim R T left right) :
    IteratorBisim R T (renameIterator A χ left) (renameIterator A χ right) := by
  exact ⟨iteratorSimulation_rename A R T hinv χ left right hbis.forward,
    iteratorSimulation_rename A R T hinv χ right left hbis.backward⟩

end RelationTransport

/-! ### Inverse-properness and witness packages -/

section Packages

/-- The ADR-06 stage-level inverse-properness package over the production carrier:
every successful stage selects a relation-preserving inverse.  Production
`STC/Core/Iterator.lean` does not define this package; the alpha layer introduces it
under the ADR-06 API name. -/
def StageInverseProper (R : RelSpec S) (it : RankedIterator S E Q) : Prop :=
  ∀ q input,
    match it.run q input with
    | .halt result => Respects R result.undo
    | .yield result _ => Respects R result.undo
    | .raise _ => True

/-- The iterator-level form of the ADR-06 inverse-properness package; production has no
separate iterator-level package beyond the stage one, so it is exactly
`StageInverseProper`. -/
def IteratorInverseProper (R : RelSpec S) (it : RankedIterator S E Q) : Prop :=
  StageInverseProper R it

/-- Stage inverse properness transports through iterator renaming under
`AlphaInvariant`. -/
theorem stageInverseProper_rename (A : AlphaAction N S) (R : RelSpec S)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N) (it : RankedIterator S E Q)
    (hproper : StageInverseProper R it) :
    StageInverseProper R (renameIterator A χ it) := by
  intro q input
  cases hrun : it.run q (A.act χ.symm input) with
  | halt result =>
      have hproper' := hproper q (A.act χ.symm input)
      rw [hrun] at hproper'
      rw [renameIterator_run_input, hrun]
      change Respects R (renameUndo A χ result.undo)
      exact respects_renameUndo A R hinv χ result.undo hproper'
  | yield result next =>
      have hproper' := hproper q (A.act χ.symm input)
      rw [hrun] at hproper'
      rw [renameIterator_run_input, hrun]
      change Respects R (renameUndo A χ result.undo)
      exact respects_renameUndo A R hinv χ result.undo hproper'
  | raise e =>
      rw [renameIterator_run_input, hrun]
      trivial

/-- Iterator inverse properness transports through iterator renaming under
`AlphaInvariant`. -/
theorem iteratorInverseProper_rename (A : AlphaAction N S) (R : RelSpec S)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N) (it : RankedIterator S E Q)
    (hproper : IteratorInverseProper R it) :
    IteratorInverseProper R (renameIterator A χ it) := by
  change StageInverseProper R (renameIterator A χ it)
  exact stageInverseProper_rename A R hinv χ it hproper

/-- The stage witness package transports through iterator renaming under
`AlphaInvariant`: the local recovery target is the acted target, and the conjugated
inverse stays proper. -/
theorem stageWitness_rename (A : AlphaAction N S) (R : RelSpec S)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N) (it : RankedIterator S E Q)
    (hw : StageWitness R it) :
    StageWitness R (renameIterator A χ it) := by
  constructor
  intro q input
  cases hrun : it.run q (A.act χ.symm input) with
  | halt result =>
      have hs := hw.stage q (A.act χ.symm input)
      rw [hrun] at hs
      rw [renameIterator_run_input, hrun]
      change R.rel (renameUndo A χ result.undo (A.act χ result.state)) input ∧
        Respects R (renameUndo A χ result.undo)
      constructor
      · simpa [renameUndo, A.act_inv, AlphaAction.alpha_act_inv_right] using
          (hinv χ _ _).1 hs.1
      · exact respects_renameUndo A R hinv χ result.undo hs.2
  | yield result next =>
      have hs := hw.stage q (A.act χ.symm input)
      rw [hrun] at hs
      rw [renameIterator_run_input, hrun]
      change R.rel (renameUndo A χ result.undo (A.act χ result.state)) input ∧
        Respects R (renameUndo A χ result.undo)
      constructor
      · simpa [renameUndo, A.act_inv, AlphaAction.alpha_act_inv_right] using
          (hinv χ _ _).1 hs.1
      · exact respects_renameUndo A R hinv χ result.undo hs.2
  | raise e =>
      rw [renameIterator_run_input, hrun]
      trivial

end Packages

/-! ### Well-founded execution transport -/

section ExecutionTransport

/-- The name-neutral execution transport: executing the renamed iterator on the acted
input is the renamed execution of the original.  The proof follows the existing rank
recursion; the success/failure tags are preserved, the conjugated inverses compose in
the same outer-after-inner order as P4, and a `raise` stage carries the unchanged
neutral error with the identity prefix undo. -/
theorem execFrom_rename_transport (A : AlphaAction N S) (χ : Equiv.Perm N)
    (it : RankedIterator S E Q) (q : Q) (s : S) :
    execFrom (renameIterator A χ it) q (A.act χ s) =
      renameExec A χ (execFrom it q s) := by
  let P : Nat → Prop := fun n => ∀ q s,
    it.rank q ≤ n →
      execFrom (renameIterator A χ it) q (A.act χ s) =
        renameExec A χ (execFrom it q s)
  have hAll : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro q s hle
        cases hrun : it.run q s with
        | halt result =>
            unfold execFrom
            rw [renameIterator_run_transport, hrun]
            rfl
        | raise error =>
            unfold execFrom
            rw [renameIterator_run_transport, hrun]
            simp [renameExec, renameFailure, renameUndo_id_fn, renameStage]
        | yield result next =>
            have hlt : it.rank next < it.rank q := it.next_lt hrun
            omega
    | succ n ih =>
        intro q s hle
        cases hrun : it.run q s with
        | halt result =>
            unfold execFrom
            rw [renameIterator_run_transport, hrun]
            rfl
        | raise error =>
            unfold execFrom
            rw [renameIterator_run_transport, hrun]
            simp [renameExec, renameFailure, renameUndo_id_fn, renameStage]
        | yield result next =>
            unfold execFrom
            rw [renameIterator_run_transport, hrun]
            simp only [renameStage, renameEffectResult]
            have hlt : it.rank next < it.rank q := it.next_lt hrun
            have hih := ih next result.state (by omega)
            cases hinner : execFrom it next result.state with
            | success inner =>
                rw [hinner] at hih
                rw [hih]
                simp only [renameExec, renameEffectResult, renameUndo_comp]
            | failure f =>
                rw [hinner] at hih
                rw [hih]
                simp only [renameExec, renameFailure, renameUndo_comp]
  exact hAll (it.rank q) q s (Nat.le_refl (it.rank q))

/-- The root-based execution convenience: production `STC/Core/Iterator.lean` exports
only `execFrom`, so the alpha transport module introduces `exec` as the explicit
root-based wrapper the ADR-06 API names. -/
def exec (it : RankedIterator S E Q) (s : S) : ExecResult S E :=
  execFrom it it.root s

/-- The name-neutral transport of root-based execution. -/
theorem exec_rename_transport (A : AlphaAction N S) (χ : Equiv.Perm N)
    (it : RankedIterator S E Q) (s : S) :
    exec (renameIterator A χ it) (A.act χ s) = renameExec A χ (exec it s) := by
  change execFrom (renameIterator A χ it) (renameIterator A χ it).root (A.act χ s) =
    renameExec A χ (execFrom it it.root s)
  rw [renameIterator_root]
  exact execFrom_rename_transport A χ it it.root s

/-- The explicit boundary contract for full-execution transport in the name-neutral
profile.  It is intentionally not claimed for name-bearing `Q`/`E` payloads; such a
profile must supply payload actions and interpreter equivariance. -/
def ExecTransportContract {N S E Q : Type v} (A : AlphaAction N S) : Prop :=
  ∀ (χ : Equiv.Perm N) (it : RankedIterator S E Q) (s : S),
    exec (renameIterator A χ it) (A.act χ s) = renameExec A χ (exec it s)

/-- The boundary contract holds in the name-neutral profile. -/
theorem execTransportContract_proof {N S E Q : Type v} (A : AlphaAction N S) :
    @ExecTransportContract N S E Q A := by
  intro χ it s
  exact exec_rename_transport A χ it s

/-- The full iterator witness package transports through iterator renaming: the stage
package transports directly, and the execution-level recovery conclusions transport
through the execution equation. -/
theorem iteratorWitness_rename (A : AlphaAction N S) (R : RelSpec S)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N) (it : RankedIterator S E Q)
    (hw : IteratorWitness R it) :
    IteratorWitness R (renameIterator A χ it) where
  stage := stageWitness_rename A R hinv χ it hw.stage
  success_recovers := by
    intro q input final h
    have htransport : execFrom (renameIterator A χ it) q input =
        renameExec A χ (execFrom it q (A.act χ.symm input)) := by
      simpa [AlphaAction.alpha_act_inv_right] using
        (execFrom_rename_transport A χ it q (A.act χ.symm input))
    cases hinner : execFrom it q (A.act χ.symm input) with
    | success inner =>
        have hfinal : final = renameEffectResult A χ inner := by
          rw [htransport, hinner, renameExec_success] at h
          cases h
          rfl
        cases hfinal
        have hrec := hw.success_recovers q (A.act χ.symm input) inner hinner
        change R.rel (renameUndo A χ inner.undo (A.act χ inner.state)) input
        simpa [renameUndo, A.act_inv, AlphaAction.alpha_act_inv_right] using
          (hinv χ _ _).1 hrec
    | failure f =>
        rw [htransport, hinner, renameExec_failure] at h
        cases h
  failure_recovers := by
    intro q input f h
    have htransport : execFrom (renameIterator A χ it) q input =
        renameExec A χ (execFrom it q (A.act χ.symm input)) := by
      simpa [AlphaAction.alpha_act_inv_right] using
        (execFrom_rename_transport A χ it q (A.act χ.symm input))
    cases hinner : execFrom it q (A.act χ.symm input) with
    | failure inner =>
        have hf : f = renameFailure A χ inner := by
          rw [htransport, hinner, renameExec_failure] at h
          cases h
          rfl
        cases hf
        have hrec := hw.failure_recovers q (A.act χ.symm input) inner hinner
        change R.rel (renameUndo A χ inner.prefixUndo (A.act χ inner.boundary)) input
        simpa [renameUndo, A.act_inv, AlphaAction.alpha_act_inv_right] using
          (hinv χ _ _).1 hrec
    | success inner =>
        rw [htransport, hinner, renameExec_success] at h
        cases h

end ExecutionTransport

end

end STC
