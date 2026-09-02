# P13-T03 Lane Handoff (DRAFT — in progress)

* Scope: `STC/Control/Rules.lean`, `STC/Examples/GlobalRules.lean`.
* Authority: lead ruling (2026-09-01) — T03 runs on top of the T02R repair
  (`61a0040` + `61ae6cf` + the ComponentSemantics universe amendment in
  `6ad1c70`). Constructor-indexed inductive rules per the ruling's table.
* Result: Rules.lean complete and clean (commit `6ad1c70`); the GlobalRules
  fixture is being repaired declaration-by-declaration with the anchor-comment
  tool (`scripts/comment_advance.py`). This file is the draft lane record and
  is kept current as the lane closes.

## Rules.lean (complete, committed `6ad1c70`)

* All section carriers pinned at ONE universe `u` so the frozen
  single-universe `StagingModel` applies (no ULift). Recorded constraint.
* Labels:
  * `GlobalOrchestrationLabel`: `insert (registrar) (fresh) (child)` — registrar
    + fresh child; `retire (owner) (before)` — the pre-retirement cell as the
    recorded child-retirement inverse linkage; `remove (owner)`.
  * `GlobalLifecycleLabel`: `begin (owner) (target ω) (flight)` — target view +
    launch token; `iter (owner) (next) (inverse) (after)` — continuation,
    yielded inverse, stage-result state; `finish (owner) (result)` — halt
    result; `divertAbort (owner) (boundary : BoundaryEvidence)` — absent or
    changed(view); `divertLand (owner) (landing) (inverse) (landed)` — landing
    token, inverse, landed state; `raise (owner) (failure)`; `leave (owner)`;
    `unload (owner) (middle)` — accumulator-result state. (Results carried in
    the labels because implicit constructor fields are unreferable in source —
    the rich-label convention.)
* Rule guards/successors (per the lead ruling):
  * `OInsert`: current+ever fresh, canonical initial cell (incarnation = fresh,
    parent = registrar registered-or-root, birth = nextBirth, inactive,
    no flight/failure), provisions disjoint from all registered → `allocate`.
  * `ORetire`: registered only (no phase guard), idempotent → `retired := true`
    via `retireState`.
  * `ORemove`: retired ∧ (inactive ∨ failed) ∧ no child → registry erase only.
  * `LBegin`: inactive ∧ ¬retired ∧ exact `TargetViewAt ω` ∧ `launch = some
    flight` → reloading, view := ω, root iterator, identity accumulator, launch
    token.
  * `LIter`: reloading ∧ target still ω ∧ real yield + rank decrease → compose
    inverse, update continuation, stay reloading.
  * `LFinish`: reloading ∧ target still ω ∧ real halt → active.
  * `LDivertAbort`: reloading ∧ boundary evidence → unloading (identity body).
  * `LDivertLand`: reloading ∧ target changed ∧ real landing → unloading,
    compose landing inverse; never active.
  * `LRaise`: (reloading ∨ active) ∧ `sem.failure failure before = some before`
    (state-preserving witness) → unloading + error recorded; never directly
    failed.
  * `LLeave`: active ∧ ¬ target-view → unloading.
  * `LUnload`: unloading ∧ ¬ (∃ dependent, ReliedUpon dependent owner) ∧
    accumulator runs → inactive/failed (by failureData), view/flight cleared;
    never erases.
* `fullRule` = the single union; `globalControlModel`/`globalStep`/`globalTrace`;
  `printedCaseOf` maps both Divert constructors to the one printed divert case;
  `ownerOf`; subfamilies `withdrawRule` (Leave+Unload), `iterationRule`
  (Begin+Iter+Finish+DivertAbort+DivertLand), `failureRule` (Raise) with
  subfamily theorems.
* Factorization (per-constructor lemmas + `fullRule_factorizes` dispatcher):
  `SelectedBody` carries the before-state guards + the body execution
  (identity/stage/flight/accumulator); `ControlEdit` is the pure successor
  equation; `BodyClass`: identity = Insert/Retire/Remove/Begin/DivertAbort/
  Raise/Leave, iterator = Iter/Finish/DivertLand, accumulator = Unload.
  Never a constant replay of the known successor.
* A.async: `divertAdmissible` over the frozen `AsyncPolicy`;
  `divertLand_has_landingWitness`, `divertAbort_atBoundary`,
  `divertLand_not_active`, `raise_not_failed`.
* R.base (ADR-08): `globalStagingModel` (singleton expandOrch/expandLife) +
  `singletonPath_orchestration/_lifecycle` + `baseOrchestration_iff`/
  `baseLifecycle_iff` + `globalStutterProfile` (iter as the only permitted
  stutter) + `orchestrationAdequacy`/`lifecycleAdequacy` +
  `globalAtomicAdequacy` — all split into lemmas.
* Frames: per-constructor D48 discharges (`insert_registrationFrame`,
  `insert_readNoninterference`, `retire_*`, `remove_*`, `lifecycle_writeFrame/
  _readNoninterference` for identity-body constructors, control-edit frames
  for the stage/accumulator ones, `unload_controlEdit_cleanupFrame`),
  `lifecycle_noAllocation` (identity-body), `iter_controlEdit_domain`.
* `failureRule_enters_teardown`, `editCell_keys`, `editCell_writeFrame`,
  `editCell_readNoninterference`, `removeState_writeFrame/_readNoninterference`.

## GlobalRules.lean (fixture — in progress)

* Carriers: Name/Key/Value := Nat; Action/Flight/Failure := Unit; Iterator/
  Accumulator := Nat; Ambient := Nat. All pure-data fixture defs (cells, states,
  views) are `abbrev` so rfl/decide/congr discharge the closed computations.
* `rulesSem` (def, committed-in-file): stage = ambient-counter guarded
  yield/halt/raise (inverse := 1, next := n-1), composeInverse := +,
  identityAccumulator := 0, accumulator adds k to ambient, launch := some (),
  flight/failure := identity, rank := ambient; all laws proved
  (by_cases + dif_pos/dif_neg + rw Nat.* to rfl; `grind only` for the
  compose/identity laws).
* Main trace (two acting fibers P=1, C=2 + auxiliaries A=3, B=4): insert/begin/
  iter/finish/retire/raise/divertAbort/divertLand/leave/unload over s0..s24;
  remove on A=3 (P=1 stays failed-registered — C is its child forever);
  providesNow_s6/s4; lookup_s1..s8/s15 lemmas (`congr`).
* ADR-09 cycle trace (p=3 former provider, r=0, c=1, n=2): the 19-step
  candidate (insert p → begin → finish → insert r → begin → finish → insert c
  (nested) → begin → iter → retire c → retire p → raise p → divertLand c →
  unload c → leave r → unload r → unload p → remove p → insert n) ending with
  parent(1)=some 0, parent(2)=some 1, n provides 20 ∧ r requires 20; endpoint
  WF theorem + precedence/freshness facts; acyclic birth chain; all names
  ever-fresh.
* A.async evidence: `rulesPolicy` (land always allowed, abort at
  `providersOf state 10 = ∅`) + divertAbort/divertLand admissibility at the
  right states.
* `factorization_nonconstant`: two iter SelectedBody witnesses (ambient 6 vs 5).

## Progress and remaining work

* Done: Rules.lean (clean); fixture head through `targetViewAt_s5_2` (live
  prefix, compiles). Frontier recoverable anytime:
  `python scripts/comment_advance.py STC/Examples/GlobalRules.lean report`.
* Remaining (fix in order with the 4-step protocol): step_begin2,
  targetViewAt_s6_2, step_iter2, step_retire2, step_insert3, step_begin3,
  step_insert4, step_begin4, step_finish4, step_retire1, step_raise1,
  noProvides10_s15, targetAbsent_s15_3, step_divertAbort3, step_unload3,
  step_retire3, step_remove3, targetNot_s19_2, step_divertLand2, step_unload2,
  step_leave4, step_unload4, step_unload1; then the A.async witnesses, the
  cycle trace (cycleStep_*), the cycle endpoint facts, cycleEndpoint_wellFormed,
  factorization_nonconstant.
* Then: T04 draft compatibility edits (Reachability.lean: `actorOf` label
  shapes, `InitialProfile`/`ReachedFrom`/`ActivationProvenance`/
  `SameOrderedOrchestrationInputs` gain a `sem` parameter or use
  `globalTrace sem`; Episode.lean likewise) — recorded as compatibility
  touches, not T04 completion.
* Then: T03 gates (focused checks, full build, scan, ledger validate,
  forbidden/import scans), finish this handoff, api-freeze T03 checkpoint,
  commit + push.

## Recorded compatibility touches (final list goes here)

* (T04 drafts, mechanical, recorded not completed): Reachability.lean,
  Episode.lean label/rule-parameter updates — to be listed when applied.
