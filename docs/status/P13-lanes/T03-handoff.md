# P13-T03 Lane Handoff (historical — superseded 2026-09-04)

> **This whole file is historical.** It was superseded by the T02R2/T03R
> repair lane: `docs/status/P13-lanes/T02R2-T03R-handoff.md` is the current
> record. The monolithic `STC/Examples/GlobalRules.lean` referenced below no
> longer exists (split into `Semantics`/`Trace`/`Evidence` modules); the
> "fixture — in progress" status and the old rich-label signature bullets
> below are obsolete; the single-file lean check command in the Gates
> section was replaced by the three-module checks. Everything below is kept
> verbatim as history only.

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

## GlobalRules fixture (SUPERSEDED by `T02R2-T03R-handoff.md`, 2026-09-04)

The bullets below describe the pre-T02R fixture and are kept as history only.
The current fixture: three modules `STC/Examples/GlobalRules/{Semantics,Trace,
Evidence}.lean`; code-ranked stage with list accumulators (`composeInverse :=
b ++ a`, identity `[]`, LIFO `foldRetire`); the main trace runs s0..s27 with
rich label payloads; the anti-vacuity mini-traces and the computable D48
coeffect write were added; `factorization_nonconstant` was replaced by
`factor_replay_nonconstant`. See the T02R2/T03R handoff for the current
inventory and gates.

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

## Result (complete, 2026-09-02)

* Rules.lean committed `6ad1c70`; the fixture fully repaired and committed
  `72592ab` (all 226 declarations green, zero warnings); A.async witnesses;
  the ADR-09 cycle trace; endpoint facts; `cycleEndpoint_wellFormed` split
  into `c19_parentClosed`/`c19_parentAcyclic`/`c19_tableConfined`/
  `c19_provisionDisjoint`/`c19_committedViewClosed`/
  `c19_committedProvidersClosed`/`c19_dataCoherent` lemmas plus the
  ten-conjunct assembly.
* Fixture data fixes forced by the authoritative guards (recorded): births
  `cell3 := 2`, `cell4 := 3` (main trace; the cycle keeps `cellP` birth 0);
  `cell4.component.iteratorCode := 0` and `cellP`/`cellR` iteratorCode `:= 0`
  (finish stages a halt, never a yield); cycle `c17 := unloadState c16 3`
  (the finish no longer composes the halt inverse, so cellP's accumulator
  stays 0); `cell1unloading`/`cell2begun`/… hoisted as abbrevs.
* `factorization_nonconstant` restated: the old same-label `m1 ≠ m2` shape
  is unprovable against the committed `SelectedBody` (every case pins
  `middle`); the evidence is now cross-label non-constancy (iter at s6,
  ambient 7, vs iter at s2, ambient 9).
* The anchor-comment tool (`scripts/comment_advance.py`) was fixed along
  the way: `advance` moves the opener forward (compiles #n+1), `checkpoint`
  moves it back; the single-anchor invariant now holds through the whole
  run.  AGENTS.md command list updated.
* Incident: the user's IDE buffer once reverted the whole fixture to the
  122-line pre-T02R file; recovered from VSCode Local History
  (`AppData/Roaming/Code/User/History/-2b0ad267/IBqV.lean`).  The recovery
  chain (memory → this file → tool report → git log) again proved out.

## Recorded compatibility touches (T04 drafts, not T04 completion)

* `STC/Control/Reachability.lean`: `actorOf` rewritten for the rich label
  shapes; `InitialProfile`/`ReachedFrom`/`Reachable`/`ActivationProvenance`/
  `RegisteredChildStep`/`SameOrderedOrchestrationInputs`/
  `SameResolvedSemanticWitnesses` take an explicit `sem` and use
  `globalTrace sem`; `ActivationProvenance.finished` carries the finish
  result; all section carriers pinned at ONE universe (the recorded
  Rules.lean restriction).
* `STC/Control/Episode.lean`: `episodeLabels`/`episodeOf`/`Factorized`/
  `episode_endpoint`/`episode_labels`/`episode_closed_status` take `sem`
  and use `globalTrace sem`; single-universe carriers.
* Both compile clean under the full build; no new theorems were added.

## Gates (all green)

* `lake build` — 3090 jobs, zero warnings; `lake env lean
  -DautoImplicit=false STC/Examples/GlobalRules.lean` clean.
* `scripts/scan_lean.py STC` exit 1 (clean); ledger 82/82, hashes OK;
  no sorry/admit/axiom in Rules/GlobalRules/Reachability/Episode;
  `git diff --check` clean.
* api-freeze T03 checkpoint appended with module SHA-256 prefixes and the
  signature inventory (see `docs/status/P13-api-freeze.md`).
