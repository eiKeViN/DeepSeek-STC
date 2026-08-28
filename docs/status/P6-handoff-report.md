# P6 handoff report: alpha transport

| Field | Value |
|---|---|
| Plan | `DH-P6-EXEC-01` (`docs/plans/P6-Execution-Plan.md`) |
| Wave | P6 — name-neutral alpha transport |
| Branch | `agent/p6-alpha` (not pushed) |
| Base commit | `a72e3d7` (`origin/main` at branch creation; matches the plan baseline) |
| Ownership | one agent, sequentially: P6-PREP → T01 → T02/T03 → T04 |

## 1. Task IDs

P6-T01 (alpha action core), P6-T02 (result/iterator/execution transport),
P6-T03 (trace/reference freshness boundary), P6-T04 (finite evidence) — all done;
the §8 gate passed.

## 2. Changed files

New files, plus two integration-owner-requested tracked edits (see below):

- `STC/Alpha/Core.lean`: the action algebra and the result-carrier actions.
- `STC/Alpha/Trace.lean`: the T03 freshness boundary. **Deliberate boundary split** per
  §3/§6: the trace section is a separate module, imported only by
  `STC.Alpha.Transport` (which re-exports it).
- `STC/Alpha/Transport.lean`: the iterator/execution transport; imports and re-exports
  `STC.Alpha.Trace`.
- `STC/Examples/Alpha.lean`: the finite `Fin 2` swap fixture.
- `STC/Bootstrap.lean`: cumulative imports (`STC.Alpha.Transport`,
  `STC.Examples.Alpha`) added on integration-owner request (2026-08-28); docstring
  extended.
- `docs/status/Definition-Ledger.json`: P6 row patch applied (see §6).
- `docs/status/P6-scan-raw.txt`: scan output (empty = clean). Integration-owned per
  §3; retained here for review, as in P3/P4.
- `docs/plans/P6-Execution-Plan.md`: the plan file, committed with the unit (P0
  precedent).

## 3. Design record

- Action convention is the ADR-06 orientation: `act (χ * ψ) x = act χ (act ψ x)`;
  no second action law, no global `Setoid`, no quotient.
- The opposite cancellation `A.act χ (A.act χ.symm x) = x` is derived, not assumed
  (`AlphaAction.alpha_act_inv_right`).
- `AlphaInvariant A R` is preserved-and-reflected (`∀ χ x y, R x y ↔ R (A.act χ x)
  (A.act χ y)`); `alphaInvariant_eq` proves equality is always invariant.
- Neutral-payload profile: `E` and `Q` are left unchanged everywhere. A `raise` stage
  acquires no fabricated state/error/undo (`renameStage_raise`); the failure
  boundary is acted on and the prefix undo conjugated.
- `renameUndo_comp` preserves P2/P4's outer-after-inner inverse order;
  `renameUndo_comp_perm` accumulates in the ADR-06 reverse order.
- `renameIterator` preserves `root`/`rank` and reuses `it.next_lt` verbatim; no new
  fuel, coinduction, or rank adjustment. `execFrom_rename_transport` follows the
  existing rank recursion (`≤`-indexed simple induction, P4 pattern).
- Production `STC/Core/Iterator.lean` exports only `execFrom`, so the alpha layer
  defines `exec` (root-based wrapper) and `ExecTransportContract` under the ADR-06
  names; it also defines `StageInverseProper`/`IteratorInverseProper` (production
  carries only `StageWitness`/`IteratorWitness`, which are transported too).
- `allocate?` returns explicit success/`none` and updates the ledger monotonically;
  `none` is plain undefinedness, never an `ExecResult.failure`. Its guard is written
  syntactically unfolded because typeclass search does not reduce compound predicate
  definitions (Lean 4.33.0 quirk, recorded in the handoff notes).
- `TraceSupport` is an explicit envelope predicate; no exact occurrence-set equality
  is claimed. No `StepEquivariant` relation was defined (§6.3 allows but does not
  require one).

## 4. Theorem inventory

No `A` (axioms), no `R0` (no new abstraction/refinement interface was introduced;
the boundary observations are `RelSpec` shells over the P5 pullback, classified `I`).

`I` (interfaces, no proof content): `AlphaAction`, `AlphaInvariant`, `renameUndo`,
`renameEffectResult`, `renameFailure`, `renameExec`, `renameStage`; `ParentRef`,
`NameLedger`, `CurrentFresh`, `EverFresh`, `LedgerSound`, `renameFinset`,
`renameParentRef`, `renameLedger`, `AllocationAllowed`, `allocate?`, `NameTrace`,
`TraceSupport`, `TraceNoReuse`, `renameNameTrace`, `AlphaBoundary`,
`renameBoundary`, `coreBoundaryObs`, `nameAwareBoundaryObs`; `renameIterator`,
`StageInverseProper`, `IteratorInverseProper`, `exec`, `ExecTransportContract`;
fixture carriers (`AlphaState`, `alphaSwap`, `alphaAct`, `alphaAction`,
`alphaIterator`, `failingIterator`, `alphaTrace`, `AlphaReport`, ...).

`K` (checked proofs; 84 total):

- Core (33): `alpha_act_inv_right`, `alphaInvariant_preserve/_reflect/_eq`;
  `renameUndo_apply/_id/_id_fn/_comp/_comp_perm/_inv/_inv'`,
  `respects_renameUndo`, `pointwise_renameUndo`; the eight rewriting equations
  (`renameEffectResult_state/_undo`, `renameFailure_error/_boundary/_prefixUndo`,
  `renameExec_success/_failure`, `renameStage_halt/_yield/_raise` — `_raise` pins
  the unchanged neutral error); the twelve `_id/_comp/_inv` laws over the four
  carriers.
- Trace (24): `renameFinset_mem/_id/_comp`, `renameParentRef_none/_id/_comp`,
  `renameLedger_everIssued/_id/_comp`, `currentFresh_rename`, `everFresh_rename`,
  `ledgerSound_rename` (iff), `allocate?_some/_none/_monotone`,
  `allocationAllowed_rename` (freshness conjuncts always transport; parent
  permission transports under its own iff hypothesis), `renameNameTrace_id/_comp`,
  `traceSupport_rename`, `traceNoReuse_rename`, `renameBoundary_id/_comp`,
  `coreBoundaryObs_ignores_trace`, `nameAwareBoundaryObs_distinguishes`.
- Transport (14): `renameIterator_root/_rank/_run_input/_run_transport` (plus the
  `next_lt` certificate inside `renameIterator`), `stageRelC_rename`,
  `iteratorSimulation_rename`, `iteratorBisim_rename`, `stageInverseProper_rename`,
  `iteratorInverseProper_rename`, `stageWitness_rename`, `iteratorWitness_rename`,
  `execFrom_rename_transport`, `exec_rename_transport`,
  `execTransportContract_proof`.
- Fixture (24): `alphaAct_refl/_swap/_inv_check/_swap_moves`,
  `alphaAction_invariant_eq`, `alphaStep_involutive`, `renameUndo_swap_check`,
  `renameEffectResult_swap_check`, `alphaNextLt`, `failingNextLt`,
  `alphaStageWitness`, `alphaExec_step`, `alphaExec_root`,
  `alphaExecTransport_eq`, `alphaExecTransport_theorem`, `alphaFailing_exec`,
  `alphaFailureTransport_eq`, `alphaTraceSupport`, `alphaTraceNoReuse`,
  `alphaTraceSupport_rename`, `alphaTraceNoReuse_rename`,
  `alphaFreshness_transport`, `alphaCoreObs_ignores`,
  `alphaNameAware_distinguishes`; plus the three `alphaAction` law fields.
  Assumptions of every relation-level theorem are exactly
  `AlphaInvariant alphaAction R.rel` (or `alphaInvariant_eq` for the equality
  specialization); the fixture uses a genuinely nontrivial swap, not only the
  identity permutation.

`E` (executable evidence): `alphaReport` pinned by `example ... := by decide` with

```text
actionSwap = true, actionInv = true, renameUndoValue = true,
allocate = true, freshness = true, traceRename = true,
coreObs = true, nameObs = true
```

The two execution rows cannot be kernel-reduced by `decide` (well-founded
`execFrom`), so they are pinned through the execution equation theorems:
`alphaExecTransport_eq` — `.success { state := (1, true), undo := renameUndo
alphaAction alphaSwap (alphaStep ∘ alphaStep) }`; `alphaFailureTransport_eq` —
`.failure { error := true, boundary := (1, true), prefixUndo := id }` (failure tag,
transported boundary, and identity prefix undo all retained).

## 5. Validation outcomes (exact)

Preflight: `git fetch origin --prune` → `origin/main` at `a72e3d7` ✓; H03/H04, all
accepted ADRs, the ADR-06 spike, and the Formal Reference match the P0-baseline
workspace hashes (including the three lead-ruled canonical variants ADR-01, ADR-02,
ADR-06-SPIKE).

```text
$ python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json   PASS, exit 0
$ python scripts/scan_lean.py STC                                                   exit 1 (clean)
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean        exit 0, no output
$ lake build                                                                         738 jobs, exit 0
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Alpha/Core.lean       exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Alpha/Trace.lean      exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Alpha/Transport.lean  exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Alpha.lean   exit 0, no output
$ lake build STC.Alpha.Core STC.Alpha.Trace STC.Alpha.Transport STC.Examples.Alpha   652 jobs, exit 0
$ python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json   PASS, exit 0 (re-run)
$ python scripts/scan_lean.py STC                                                   exit 1 (clean), raw in P6-scan-raw.txt
```

Scanner interpretation: exit `1` = clean (no lexical match), per the project
protocol; the raw output is empty.

## 6. Ledger row patch (applied 2026-08-28; validator PASS)

```text
D45  (retain in_progress/seam_only) notes: add "P6: explicit freshness-boundary
     product (AlphaBoundary) delivered; provider adequacy and active-store semantics
     remain deferred"
D53  delivery_status: planned -> in_progress; evidence_state: aligned -> seam_only;
     notes: "P6: NameLedger/NameTrace/TraceSupport/TraceNoReuse shell delivered;
     lifecycle/control trace decomposition remains BD-CONTROL"; deferred_reason drops
     the resolved P6 clause
L56  delivery_status: planned -> in_progress; evidence_state: pending -> proved;
     notes: "P6: name-neutral execFrom/exec transport checked (ExecTransportContract);
     named Q/Xi/payload variant remains deferred"; deferred_reason drops the resolved
     P6-T03 clause
D60  delivery_status: planned -> in_progress; evidence_state: pending -> proved
     (per plan §9: retain the P4 transport/iterator evidence — the P4-proposed status
     had not yet been applied); notes combine P4 stageCountFrom and P6 transports
T73  (retain planned/pending) notes: "P6: alpha-support and no-reuse transport
     evidence only; support/confluence remains BD-SUPPORT + BD-CONTROL"
D65, L68, L71, L72  (retain statuses) notes: "P6: no completion claim from P6 alone"
```

`BD-CONTROL`, `BD-SUPPORT`, `BD-STAGING`, `BD-SCOPED` stay in place.
`python scripts/validate_definition_ledger.py` PASS after the patch.

## 7. Deferred obligations

- Named-payload profile: `RenameQ`/`RenameXi` actions plus interpreter/run
  equivariance (ADR-06 payload boundary; §5.3).
- Authoritative labelled control constructors, nested-allocation coverage, and
  operational lifecycle semantics (BD-CONTROL, ADR-07/08).
- Episode/support/precedence reindexing and L68/L70/L72/T73 (BD-SUPPORT, ADR-09);
  scoped coeffects (BD-SCOPED, ADR-10).
- Exact occurrence-set equality for real lifecycle traces; allocation-completeness;
  operational `StepEquivariant` contracts (deliberately not defined here).
- `(runtime atom, generation) → IncarnationId` refinement and stale-handle safety
  (future runtime-refinement phase, `STC.Adapter`).

## 8. Frozen/shared confirmation

No H03/H04, ADR, Blueprint, spike, or P1–P5 module was modified.
`STC/Core/Iterator.lean` and `STC/State/**` untouched. On integration-owner request
(2026-08-28): `STC/Bootstrap.lean` gained the cumulative alpha imports and
`Definition-Ledger.json` received the §6 patch; `STC.lean` is unchanged (it already
imports `STC.Bootstrap`). Post-integration gate: Bootstrap exit 0, `lake build` 754
jobs exit 0, scan exit 1.

## 9. Notes for the integration owner

- `P6-scan-raw.txt` is integration-owned; retained here per P3/P4 precedent.
- Lean 4.33.0 quirks hit and worked around: typeclass search does not unfold
  compound predicate defs (allocate? guard unfolded); `cases h : e` generalizes
  goal occurrences of `e`; `cases p0` clears `p0`; `subst` on dependent hypotheses
  can eat rcases-bound context; `change`/`rw` can fail to reduce exposed match-def
  constructor applications where `simp only [defs]` succeeds; `omit [X] in` must
  precede the docstring; `Finset.insert` is only the `Insert` typeclass instance.

## Unresolved Questions

1. The P3/P4/P5 ledger patches beyond §6 (D51, D52, T66, R.iter, ...) and the
   P3/P4 cumulative imports (`STC/Core/Partial`, `STC/Core/Iterator`,
   `STC/Examples/TwoCounter`, `STC/Examples/VerticalSlice`) are still not applied
   to `STC/Bootstrap.lean`/`Definition-Ledger.json` — apply them next?
