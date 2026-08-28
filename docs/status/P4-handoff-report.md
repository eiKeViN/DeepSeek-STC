# P4 handoff report: ranked iterator

| Field | Value |
|---|---|
| Plan | `DH-P3-P4-EXEC-01` (`docs/plans/P3-P4-Execution-Plan.md`) |
| Wave | P4 — ranked iterator |
| Branch | `agent/p3-p4` (not pushed) |
| Base commit | `0971772` (`origin/main` at branch creation) |
| P4 commits | `bbf6699` (iterator + recovery), `231925c` (nested evidence) |
| Ownership | one agent, P3 then P4 sequentially; P5 runs in parallel (untouched) |

## 1. Task IDs

P4-T01 (ranked machine), P4-T02 (well-founded execution + prefix undo),
P4-T03 (relation/witness interfaces), P4-T04 (nested tests) — all done; P4 gate passed.

## 2. Changed files and public declarations

- `STC/Core/Iterator.lean` (new): `StageResult`, `RankedIterator`, `execFrom`;
  `execFrom_halt`, `execFrom_raise`, `execFrom_yield_success`, `execFrom_yield_failure`;
  `stageCountFrom`, `stageCountFrom_le`;
  `execFrom_recovers`, `execFrom_success_recovers`, `execFrom_failure_recovers`;
  `StageRelC`, `IteratorSimulation`, `IteratorBisim`, `ContinuationStable`,
  `StageWitness`, `IteratorWitness`, `iteratorWitness_of_stageWitness`, `execFrom_rel`.
- `STC/Examples/VerticalSlice.lean` (new): `Control`, `counterRun`, `counterRank`,
  `counterIterator`, `failingRun`, `failingIterator`, `counterNextLt`, `failingNextLt`,
  `counterStageWitness`; `s0`–`s4`, `execCount0`–`execCount3`, `counterExec_eq`,
  `failingExec_eq`, `stageCount_eq`; `successFinal`, `successRecovered`,
  `failureBoundary` + their `_eq` theorems; `stageMixed_not_rel`,
  `stageMixedRejected`, `execSuccess_refl`, `execReflCheck`, `SliceReport`,
  `sliceReport`.

## 3. Design record

- `execFrom` is well-founded recursion on the rank certificate (`termination_by
  it.rank q`), no fuel, no coinductive loop. `Q` is external control data.
- Every failure retains `error`, `boundary`, `prefixUndo`; a `raise` stage yields no
  new state or inverse. No parallel failure carrier was introduced.
- Induction over executions uses a core-only `≤`-indexed simple induction
  (`P n := ∀ q input, rank q ≤ n → …`), since `Nat.strong_induction_on` is
  mathlib-only and this module deliberately imports no Mathlib.

## 4. Theorem inventory

K (checked proofs):

- generic: the four execution equations; `execFrom_recovers` and both explicit
  corollaries (success recovery through the composed inverse, failure recovery
  through the successful-prefix inverse at the boundary) under per-stage local
  recovery + inverse properness only; `stageCountFrom_le` (rank q + 1 stages);
  `iteratorWitness_of_stageWitness`; `execFrom_rel` (simulation transport with a
  left stage witness; input-relatedness is part of the statement).
- instance: `counterNextLt`, `failingNextLt` (the rank certificates);
  `counterStageWitness` (equality specialization); `counterExec_eq`,
  `failingExec_eq`, `stageCount_eq` (the computed traces);
  `stageMixed_not_rel`, `execSuccess_refl` (the relation checks).

I: `StageRelC`, `IteratorSimulation`, `IteratorBisim`, `ContinuationStable`,
`StageWitness`, `IteratorWitness` — no global `Setoid`, no identification of `≃`/`≈`.

E (pinned report; equation-pinned because `decide` cannot kernel-reduce the
well-founded `execFrom`):

```text
sliceReport =
  { successFinal := (5, 7), successRecovered := (0, 7), stageCount := 5,
    failureBoundary := true, stageMixedRejected := true, execRefl := true }
```

## 5. Validation outcomes (exact)

```text
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Core/Iterator.lean         exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/VerticalSlice.lean exit 0, no output
$ lake build                                                                               642 jobs, exit 0
$ python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json          PASS, exit 0
$ python scripts/scan_lean.py STC                                                          exit 1 (clean), raw in docs/status/P4-scan-raw.txt
```

## 6. Ledger row patch (NOT applied; integration owner applies after review)

```text
D51  delivery_status: planned -> completed; evidence_state: pending -> proved;
     notes: "P4-T01/T03: RankedIterator carrier with strict-successor certificate,
     StageWitness/IteratorWitness, StageRelC/IteratorSimulation/IteratorBisim delivered"
D52  delivery_status: planned -> completed; evidence_state: pending -> proved;
     notes: "P4-T02: execFrom by well-founded rank recursion, LIFO inverse
     composition, success and failure prefix-recovery theorems, execution equations"
D60  delivery_status: planned -> in_progress; evidence_state: pending -> proved;
     notes: "P4: stageCountFrom and stageCountFrom_le delivered; reach-closed
     iteration monoids remain deferred (BD-CONTROL)"
T66  delivery_status: planned -> in_progress;
     notes: "P4: rank termination bound proved (stageCountFrom_le); global lifecycle
     suffix theorem remains deferred (BD-CONTROL, F-T66-ORIGIN)"
R.iter  delivery_status: planned -> in_progress; evidence_state: pending -> proved;
     notes: "P4: iterator execution slice (execFrom, equations, nested success/failure
     traces) delivered; L-Begin/L-Iter/L-Finish constructors remain deferred (BD-CONTROL)"
```

## 7. Counterexamples and vacuity checks

- The failing trace raises at the boundary `(1, 0)` with prefix undo recovering
  `(0, 0)` — visibly retained, not an identity or input rewrite.
- `stageMixed_not_rel` proves the mixed-tag pair is rejected; `execSuccess_refl`
  proves reflexivity of the equality specialization.
- The rank certificates are per-constructor `K` proofs; no stage allows a
  non-decreasing yield (P4-T04 negative rank obligation covered by the certificates,
  not by evaluating a malformed `RankedIterator`).

## 8. Frozen/shared confirmation

No H03/H04, ADR, Blueprint, spike, `STC.lean`, `STC/Bootstrap.lean`, or
`Definition-Ledger.json` file was modified. P1/P2/P3 APIs used as-is.

## 9. Downstream notes

- P7 (TwoCounter/VerticalSlice owners) may extend the two example files after P6;
  the P3/P4 fixtures are staged as planned.
- The `decide`-over-WF-def limitation and the other Lean 4.33.0 quirks are recorded
  in the P3 handoff §9 for the integration owner.

## Unresolved Questions

1. Integration owner: apply the ledger patch in §6 after review?
2. Cumulative `STC/Bootstrap.lean` imports by the integration owner?
