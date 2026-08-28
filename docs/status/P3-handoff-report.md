# P3 handoff report: partial operations and failure

| Field | Value |
|---|---|
| Plan | `DH-P3-P4-EXEC-01` (`docs/plans/P3-P4-Execution-Plan.md`) |
| Wave | P3 — partial operations and failure |
| Branch | `agent/p3-p4` (not pushed) |
| Base commit | `0971772` (`origin/main` at branch creation) |
| P3 commits | `e9777e9` (contracts), `efb0451` (evidence) |
| Ownership | one agent, P3 then P4 sequentially; P5 runs in parallel (untouched) |

## 1. Task IDs

P3-PREP (D17/L18 disposition), P3-T01, P3-T02, P3-T03, P3-T04 — all done; P3 gate passed.

## 2. Changed files and public declarations

- `STC/Core/Partial.lean` (new): `OpResult`, `PartialOp`, `PartialMap`, `pcomp`,
  `totalPartialOp`, `DefinedAt`, `OpResultRel`, `opResultRelSpec`, `pcompOp`;
  `WeakOperationRespects`, `OperationRespects`, `DefinednessStable`, `OutcomeStable`,
  `SelectedInverseCoherent`, `SelectedInverseStableOp`, `OperationRecovers`,
  `OperationForeignStability`, `EffectIndependence`, `OperationIndependenceContract`;
  `operationRespects_definednessStable`, `operationRespects_outcomeStable`,
  `operationRespects_selectedInverseCoherent`, `pcomp_assoc`,
  `totalPartialOp_respects`, `totalPartialOp_recovers`, `totalPartialOp_stable`;
  `opResultToEffectResult`, `opResultToExecSuccess`, `partialOpToExec`,
  `partialOpToExec_some`, `partialOpToExec_none`.
- `STC/Foundation/Result.lean` (additive only): `effectResultToExec`.
  No P1/P2 declaration or theorem statement was changed.
- `STC/Examples/TwoCounter.lean` (new): `CounterState`, `inc1`, `inc2`, `dec1`,
  `failIfZero`, `inc1_lawful`, `inc2_lawful`, `failIfZero_atomic`,
  `inc12_independent`, `fstProjectOp_not_foreignStable`, `failAfterInc`,
  `CounterFailureReport`, `counterFailureReport`.

## 3. P3-PREP disposition (D17/L18)

**Deferred.** The P2 `Transformation` API does not include the generated
transformation-monoid closure D17/L18 needs, and an additive companion would be a
large standalone effort. Per the plan's fallback branch, only the relation-level
independence contracts were implemented. T20/C21 are **not** marked proved and carry
a precise deferred obligation (see ledger patch below). No new semantic decision was
made.

## 4. Theorem inventory

K (checked proofs):

- generic: `pcomp_assoc`; `opResultRelSpec`; the three contract decompositions;
  `totalPartialOp_respects`/`_recovers`/`_stable`; `partialOpToExec_some`/`_none`.
- instance: `inc1_lawful`, `inc2_lawful` (equality specialization);
  `failIfZero_atomic` (Toy atomicity); `inc12_independent` (positive law);
  `fstProjectOp_not_foreignStable` (negative countermodel).

I (elaboration only): all of `STC/Core/Partial.lean` and `STC/Examples/TwoCounter.lean`.

E (finite decidable evidence, pinned):

```text
counterFailureReport =
  { incRecovers := true, failZeroUndefined := true, failNonzeroDefined := true,
    failStateUnchanged := true, decZeroUndefined := true, decDefinedState := true,
    optionMixedRejected := true, failureBoundary := true }
```

`failAfterInc` computes the failure boundary `(1, 0)` and the prefix inverse
recovering `(0, 0)`. No `#eval` over exposed declarations (Windows shared-library
constraint, AGENTS.md).

## 5. Validation outcomes (exact)

```text
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Foundation/Result.lean   exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Core/Partial.lean        exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/TwoCounter.lean exit 0, no output
$ lake build                                                                            642 jobs, exit 0
$ python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json       PASS, exit 0
$ python scripts/scan_lean.py STC                                                       exit 1 (clean), raw in docs/status/P3-scan-raw.txt
```

## 6. Ledger row patch (NOT applied; integration owner applies after review)

```text
D17  delivery_status: planned -> deferred;   evidence_state: pending -> deferred;
     deferred_reason: "P3-PREP: generated transformation closure deferred; relation-level
     independence contracts implemented without it"
L18  same as D17
D19  delivery_status: planned -> completed;  evidence_state: pending -> proved;
     notes: "P3-T02: EffectIndependence, OperationIndependenceContract,
     OperationForeignStability delivered; inc12_independent (K) positive law;
     fstProjectOp_not_foreignStable (K) countermodel"
T20  deferred_reason: "depends on deferred D17/L18 generated closure (P3-PREP); not proved"
C21  deferred_reason: "depends on deferred D17/L18 generated closure (P3-PREP); not proved"
D23  delivery_status: planned -> in_progress;
     notes: "P3-T01: OpResult/PartialOp carrier delivered; concrete coeffect get/set
     transitions remain P5/ADR-02"
D24  delivery_status: planned -> in_progress; notes: same as D23
D25  delivery_status: planned -> in_progress; notes: "P3-T01: outcome payload delivered;
     semantic/executable specs remain ADR-02/P5"
D26  delivery_status: planned -> in_progress; notes: same as D25
D34  delivery_status: planned -> in_progress; notes: "P3-T01: outcome carriers and relators
     delivered; typed test AST remains P5"
D39  delivery_status: planned -> in_progress; evidence_state: pending -> proved;
     notes: "P3-T02: DefinednessStable/OutcomeStable/SelectedInverseCoherent/
     OperationIndependenceContract delivered with instance proofs; key commutativity
     remains P5/ADR-02"
R.fail  delivery_status: planned -> in_progress; evidence_state: pending -> proved;
     notes: "P3-T03/T04: failure outcome, bridge (effectResultToExec, partialOpToExec),
     boundary and prefix-undo evidence delivered; L-Raise constructors remain deferred
     (BD-CONTROL)"
```

## 7. Counterexamples and vacuity checks

- Foreign-stability countermodel: `fstProjectOp` with the fst-projection selected
  inverse does not commute with `swapCounters` even up to equality
  (`fstProjectOp_not_foreignStable`, concrete witness `(1, 2)`).
- Definedness is witness-carrying (`∃ r, op input = some r`), so no contract can be
  discharged vacuously by an unreachable `some`.
- `OptionRel` mixed-tag rejection pinned (`optionMixedRejected`).

## 8. Frozen/shared confirmation

No H03/H04, ADR, Blueprint, spike, `STC.lean`, `STC/Bootstrap.lean`, or
`Definition-Ledger.json` file was modified. P1/P2 APIs untouched (only additive
`effectResultToExec` in `Foundation/Result.lean`).

## 9. Toolchain findings for the integration owner

Lean 4.33.0 (pinned) quirks hit and worked around; recommend an AGENTS.md note:

1. `∀ …, P → (Q ↔ R)` statements fail to elaborate (`introN`/term mode) — even
   `True ↔ True`; paired arrows `(Q → R) ∧ (R → Q)` work. Used in `DefinednessStable`.
2. `simp` does not reduce closed `if` conditions; `rfl`/`decide` do.
3. `rw` on `termination_by` definitions works only on the first rule per call
   (no inter-rule iota); `unfold` + split `rw` + `simp only []` between.
4. `decide` cannot kernel-reduce well-founded-fix definitions (`execFrom`,
   `stageCountFrom`) — pin reports via equation theorems instead.
5. Structure literals in theorem statements with projection-valued fields
   (`{ error := f.error, … }`) fail to parse; anonymous constructors `⟨…⟩` work.
6. `pick_goal`/`Nat.strong_induction_on` are mathlib-only; core has neither — the
   `≤`-indexed simple induction pattern used in `Iterator.lean` is core-only.

## Unresolved Questions

1. Integration owner: apply the ledger patch in §6 after review?
2. Cumulative `STC/Bootstrap.lean` imports of the P3/P4 modules by the integration
   owner (P3/P4 deliberately did not edit Bootstrap per the parallel-work lock)?
