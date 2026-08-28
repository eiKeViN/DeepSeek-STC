# P7 Handoff Report: Two-Counter Vertical Slice

| Field | Value |
|---|---|
| Plan | `DH-P7-P8-EXEC-01` (`docs/plans/P7-P8-Execution-Plan.md`) |
| Wave | P7 — two-counter vertical slice |
| Branch | `codex/adr07-10-reconcile-p7-p8` |
| P7 base | `d2f8caa` (`origin/main`), with reconciliation checkpoint `4128405` |
| P7 implementation commits | `f0bb5e7`, `6b0dbcd`, `29004df`, `c436bf2`, `aedd534` |
| Toolchain | Lean 4.33.0 / Lake 5.0.0-src+d8b1897 / Mathlib v4.33.0 |
| Gate date | 2026-08-28 |

## Task status

| Task | Result |
|---|---|
| P7-PREP | Passed: P6 alpha API, existing P3/P4 fixtures, and baseline gates audited |
| P7-T01 | Passed: symmetric `dec2` carrier, guard, successor, inverse, and finite checks |
| P7-T02 | Passed: exact increment recovery, defined decrement recovery/stability, and explicit observation theorem |
| P7-T03 | Passed: exact `inc1`/`inc2` commutation and non-vacuous foreign-stability counterexample |
| P7-T04 | Passed: additive ranked success/failure iterators, strict rank certificates, and equation-pinned traces |
| P7-T05 | Passed: non-identity `Fin 2` swap, used name-bearing trace fields, execution transport, and observation split |
| P7-T06 | Passed: integrated recovery corollaries and expanded finite report |

## Production changes

`STC/Examples/TwoCounter.lean` retains the P3 fixtures and adds `dec2`,
`dec1_recovers_defined`, `dec2_recovers_defined`, selected-inverse stability,
the explicit `secondCounterObservation`, exact increment recovery, exact
commutation, and the finite foreign-stability mismatch.

`STC/Examples/VerticalSlice.lean` preserves the original five-stage P4
`counterIterator`/`failingIterator` equations and adds `twoCounterIterator`
(`inc1` then `inc2` then halt), `twoCounterFailureIterator` (`inc1` then
`failIfZero` at `(1, 0)`), their strict rank and recovery witnesses, exact
success/failure execution equations, stage counts, and generic
`execFrom_*_recovers` corollaries.

The alpha regression uses `twoCounterSwap : Equiv.Perm (Fin 2)` with a genuinely
used `NameTrace`: allocations `[1]`, a `some 1` reference, parent metadata, and
boundary snapshots.  The state action follows P6's neutral-payload profile;
`twoCounterAlphaExec_transport` and `twoCounterAlphaFailureExec_transport`
apply the checked execution transport theorem.  Core observation relates the
same state despite renamed trace metadata, while the explicit name-aware
observation rejects that boundary pair.

## Expected finite report

The exposed `example` in `VerticalSlice.lean` pins:

```text
legacy P4: successFinal=(5,7), successRecovered=(0,7), stageCount=5,
           failureBoundary=true, stageMixedRejected=true, execRefl=true
P7:        successFinal=(1,1), successRecovered=(0,0), stageCount=3,
           failureBoundary=true, failureStageCount=2, successInverse=true,
           independence=true, foreignStabilityCounterexample=true,
           rankChecks=true, alphaSwapMoves=true, alphaTraceSupport=true,
           alphaTraceNoReuse=true, alphaCoreObservation=true,
           alphaNameAwareObservation=true
```

The canonical failure remains an `ExecResult.failure` with `error=()`,
`boundary=(1,0)`, and the `inc1` prefix inverse; it is never represented as
`Option.none`, identity success, or an input-state rewrite.

## Gate evidence

```text
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/TwoCounter.lean
  exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/VerticalSlice.lean
  exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
  exit 0, no output
$ python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
  exit 0, Definition-Ledger validation: PASS (82/82; H03/H04 hashes OK)
$ lake build
  exit 0, Build completed successfully (756 jobs)
$ python scripts/scan_lean.py STC
  exit 1, clean; raw record retained in docs/status/P7-scan-raw.txt
$ git diff --check
  exit 0
```

No P3/P4 theorem statement or P6 action convention was changed.  The Definition
Ledger, frozen H03/H04 inputs, and accepted ADR-01..06 artifacts were not edited.
P7 earns finite `I`/`K`/`E` evidence for the concrete slice only; it does not
establish the proposed ADR-07..10 architecture, Section-4 lifecycle/control
theorems, or any Cordis `R1+` refinement.  `BD-CONTROL`, `BD-STAGING`,
`BD-SUPPORT`, `BD-SCOPED`, and runtime-refinement obligations remain explicit.
