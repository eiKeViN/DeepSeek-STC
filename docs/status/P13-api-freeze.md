# P13 API Freeze

| Field | Value |
|---|---|
| Plan | `DH-P13-GLOBAL-METATHEORY-EXEC-01` |
| Base | `96b8752` (`P13 plan added`) |
| Freeze state | T03 re-frozen (2026-09-04, T02R2/T03R lane); T04 released |
| Toolchain | Lean 4.33.0 / Mathlib v4.33.0 |

## T02 checkpoint (positive state and model API freeze)

* Branch: `codex/p13-continuation`; base for this checkpoint: `8ae8ab5`
  (T01C close); checkpoint commit: `db9d180`.
* Modules: `STC/State/Component.lean` (unchanged from the review draft),
  `Fiber.lean`, `Global.lean`, `Global/Observation.lean`,
  `Examples/GlobalModel.lean`.
* Cross-lane compatibility touches (minimal, recorded in the T02 handoff):
  `STC/Examples/GlobalRules.lean` (`cell0.committedView`) and
  `STC/Control/Reachability.lean` (`RelatedCell` compares committed provider
  views through the growing bijection).
* Dropped unfrozen draft names: `ProviderModel` (replaced by executable
  `providersOf` plus proved laws), placeholder `TargetView` (replaced by
  per-fiber `targetView`/`targetProviders`), `toPositiveContext`
  (the T01C `PositiveContext` shares one universe between ambient and code,
  so the mixed-universe ambient pairing cannot instantiate it; the D32
  representation is delivered at the registry level and the limitation is
  recorded in the handoff).
* T01C frozen-interface notes for T02: the concrete D33
  `ObservationKit` assembly is uniform-universe because the T01C
  `ObservationKit` shares universes between its carriers; the mixed-universe
  component instantiations `registryObservation`/`committedObservation` are
  kept alongside.
* SHA-256 (module files):
  * `STC/State/Component.lean`
    `c4461baf9b0796748bbc57139d6410f008fb9c4002dccdd26a97707c33e12bab`
  * `STC/State/Fiber.lean`
    `060ce54a855c07892325655d680805a5fbc271e6f2ba5d2451876c81bed14685`
  * `STC/State/Global.lean`
    `f1b0e99e6217f4fea26131d7be9d73fdd94ed98b64b6086d7e40113cdda92304`
  * `STC/State/Global/Observation.lean`
    `ce0afa265d18d57ea122b2d7baff7777de10467c85b9050cda4a2122cb6f1201`
  * `STC/Examples/GlobalModel.lean`
    `b7a74a40950b35742ae142c115928803706f45e89facedc64d92ed4aeaf560a1`
* Focused checks: `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true`
  on each of the five modules plus the two compatibility-touched files,
  exit 0, zero warnings.
* Full build: `lake build` completed successfully (3090 jobs, exit 0).
* Gates: `scripts/scan_lean.py STC` exit 1 (clean);
  `scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json`
  82/82 with both frozen H03/H04 hashes OK; forbidden-token and
  import-boundary scans exit 1 (no matches); `git diff --check` clean;
  protected-path diffs clean.

## T02R checkpoint (semantic-view/profile repair, lead-ruled)

* Authority: lead decision (2026-09-01) inserting a repair between the
  T02 freeze and T03; no new ADR, no `FiberCell`/`GlobalState` carrier
  fields changed. Lane record: `docs/status/P13-lanes/T02R-handoff.md`.
* Branch: `codex/p13-continuation`; base for this checkpoint: `c247991`;
  checkpoint commit: `61a0040`.
* Modules: `STC/State/Component.lean` (stage semantics repair),
  `STC/State/Global.lean` (view/WF/D48 repair),
  `STC/Examples/GlobalModel.lean` (fixture on the repaired semantics).
* SHA-256 (module files):
  * `STC/State/Component.lean`
    `ce759d9a2c536c89c48a522c15e7b1271750a993e31460716aa75e0dcacca3d4`
  * `STC/State/Global.lean`
    `e6a9c02061221f87e41e1938e184ad564e312ee732af56fcb2c0e5d5c3ccc21f`
  * `STC/Examples/GlobalModel.lean`
    `79191db2d8032d2defed68912a8c97b283575e6320cd189fb5b54be1a4c41d08`
* Superseded T02 surface: `ProvidesNow` is now active ∧ committed-table
  membership with no retired check; `CommittedProvides` added for
  teardown views; `TargetViewAt`/`TargetAbsent` replace the
  `Option (Finset Name)` view as the rule input; `Registered` split from
  the phase-based `Installed`; `ReliedUpon` gains the distinct/installed/
  required-key envelope; `Quiescent` aligns active views with targets;
  `CommittedProvidersClosed` uses `CommittedProvides`; `WellFormed`
  grows to ten conjuncts (five new data-coherence conditions);
  `ComponentSemantics.iterator` is replaced by `stage` +
  `StageResult` + the composition/identity/launch machinery; the D48
  surface is split into `WriteFrame`/`ReadNoninterference`/
  `ReadRespect`/`RegistrationFrame`/`CleanupFrame`.
* Focused checks on the three modules: exit 0, zero warnings.
* Full build: `lake build` completed successfully (737 targets, exit 0).
* Gates: scan exit 1 (clean); Ledger validator 82/82 with both frozen
  H03/H04 hashes OK; forbidden-token and import-boundary scans exit 1;
  `git diff --check` clean; no cross-lane files touched.

## Current production surface

The P13 production graph is additive and data-positive:

```text
Core/Effect/Closure + Core/Partial/Recovery + Core/Coeffect
  -> State/Positive + State/Observation/Lift + Relation/Transport
  -> State/Component + State/Fiber + State/Global + Global/Observation
  -> Control/Rules -> Control/Reachability + Control/Episode
  -> Control/Structural, Preservation, Recovery, Support, Spatial, Progress,
     Alpha, Commutation -> Control/Deletion -> Control/Canonical
  -> Conformance/Global
```

The carrier retains `NameLedger.everIssued` and an ordered `allocationHistory`.
`GlobalState` stores only finite maps, records, codes, phases, and data. The
semantic interpreter/profile fields are external to the carrier. `fullRule` is
the sole union of `orchestrationRule` and `lifecycleRule`; `withdrawRule`,
`iterationRule`, and `failureRule` are derived constructor views.

## Signature inventory

* `STC.State.GlobalState`, `allocate`, `nextBirth`, `retire?`,
  `updateFiber` + frame laws, `activeNames`, `activeStore`, `stableImage`,
  `ProvidesNow` (table-based), `CommittedProvides`, `providersOf` +
  `_sound/_complete/_unique/_card_le_one`,
  `targetProviders`, `targetSatisfied`(+`_iff`), `targetView` +
  `_isSome_iff/_some_iff/_mem/_provides`, `TargetViewAt`, `TargetAbsent`,
  `Registered`, `Installed`, `installed_registered`, `Failed`,
  `PendingFlight`, `Quiescent` (target-aligned), `WriteFrame`,
  `ReadNoninterference`, `ReadRespect`, `RegistrationFrame`,
  `CleanupFrame`, `allocate_registrationFrame`, `updateFiber_cleanupFrame`,
  `retire?_cleanupFrame`, `updateFiber_readRespect`,
  `ReliedUpon`(+`_iff_view`), `ParentStep`, `ParentClosed`,
  `ParentAcyclic`, `TableConfined`, `ProvisionDisjoint`,
  `CommittedViewClosed`, `CommittedProvidersClosed`,
  `ActiveTableCoherent`, `CommittedViewDomain`, `IncarnationCoherent`,
  `AllocationCoherent`, `LedgerCoherent`, `DataCoherent`,
  `WellFormedProfile` (lifecycleCoherent/root/declarations), `WellFormed`
  (ten conjuncts) + nine retained and five new `wellFormed_*`
  projections, `FiberData`, `FiberCode`, `toPositiveRegistry`
  + `_entries/_keys`, `toPositive_lookup_some/_none/_isSome_iff`,
  `PositiveCellObs`, `AlphaCodeProfile`, `NameNeutral`,
  `FactorizationProfile`, `ProgressProfile`, `ConfluenceProfile`.
* `STC.State.ComponentSemantics` (T02R shape): `action`, `stage` +
  `StageResult` (yield/halt/raise, `state`/`inverse?`/`failure?`),
  `composeInverse`, `identityAccumulator`, `launch`, `flight`, `failure`,
  `undo`, `observes`, `writesWithinProvision`, `continuationStable`,
  `rank`, `accumulatorFrame`, and the checked law fields.
* `STC.State.Global.Observation`: `GlobalObservation`, `StateObs` + five
  projections + `_refl/_symm/_trans`, `registryObservation`,
  `committedObservation`, `observationKit`, `stateObs_eq_lifted`
  (uniform-universe assembly; see the T02 checkpoint note).
* `STC.Control.GlobalOrchestrationLabel`, `GlobalLifecycleLabel`,
  `orchestrationRule`, `lifecycleRule`, `fullRule`, `globalControlModel`.
* `STC.Control.InitialProfile`, `ReachedFrom`, `Reachable`, `Episode`,
  `ActivationProvenance`, `GrowingBijection`, `RelatedCell`,
  `SameOrderedOrchestrationInputs`,
  `SameResolvedSemanticWitnesses`.
* `STC.Control.StructuralLaws`, `PreservationProfile`, `RecoveryProfile`,
  `SpatialProfile`, `ProgressMeasure`, `RuleAlphaProfile`, `DiamondProfile`,
  `DeletionEnvelope`, `CanonicalEnvelope`, `ConfluenceEnvelope`.
* `STC.Conformance.p13Entries`, `p13Deferred`, and `globalManifestShape`.


## T03 checkpoint (2026-09-02, commit 72592ab + follow-ups)

* `STC.Control.Rules` (commit `6ad1c70` + T03): the constructor-indexed
  authoritative rule surface.  Labels are rich payloads:
  `GlobalOrchestrationLabel` — `insert (registrar) (fresh) (child)`,
  `retire (owner) (beforeCell)`, `remove (owner)`;
  `GlobalLifecycleLabel` — `begin (owner) (ω) (flight)`,
  `iter (owner) (next) (inverse) (after)`, `finish (owner) (result)`,
  `divertAbort (owner) (BoundaryEvidence absent|changed)`,
  `divertLand (owner) (landing) (inverse) (landed)`,
  `raise (owner) (failure)`, `leave (owner)`, `unload (owner) (middle)`.
  `OrchestrationRule`/`LifecycleRule sem` with the lead-ruling guards;
  `fullRule`, `globalControlModel`, `globalStep`, `globalTrace`;
  per-constructor successors (`allocate`, `retireState`, `beginState`,
  `iterState`, `finishState`, `divertAbortState`, `divertLandState`,
  `raiseState`, `leaveState`, `unloadState`, `removeState`);
  factorization (`SelectedBody`/`ControlEdit`/`BodyClass` +
  `factor_*`/`fullRule_factorizes`); A.async (`divertAdmissible`);
  R.base staging (`globalStagingModel`, adequacy, stutter profile);
  D48 frames per constructor.  ALL section carriers pinned at ONE
  universe (recorded restriction carried by T04 too).
* `STC.Examples.GlobalRules` (fixture, commit `72592ab`): inhabits every
  constructor over the two-fiber main trace plus the ADR-09 three-edge
  cycle trace, endpoint facts, `cycleEndpoint_wellFormed` (split into
  `c19_*` per-conjunct lemmas), and `factorization_nonconstant`
  (cross-label non-constancy; the old same-label m1≠m2 shape is
  inconsistent with the committed `SelectedBody`, which pins the middle).
* `STC.Control.Reachability` / `STC.Control.Episode` (T04 drafts,
  compatibility touches): `actorOf` new label shapes;
  `InitialProfile`/`ReachedFrom`/`Reachable`/`ActivationProvenance`/
  `RegisteredChildStep`/`SameOrderedOrchestrationInputs`/
  `SameResolvedSemanticWitnesses` take an explicit `sem` and use
  `globalTrace sem`; carriers pinned at one universe; `Episode`
  single-universe.  Recorded, not T04 completion.
* Module SHA-256 prefixes: Rules `447c2668…`, GlobalRules `8452d741…`,
  Reachability `d39c0bc5…`, Episode `ceecf4e1…`.

## T03 re-freeze checkpoint (2026-09-04, T02R2/T03R lane, commits 7742455..6155898)

* `STC.Control.Rules` (T02R2/T03R repair, tasks 1-5 + blockers): the
  `ComponentSemantics` surface above with `Key` first, `FailureEvidence`,
  envelope fields, `writesWithinProvision`, `BodyFrameAdequacy`
  (`provision_coeffectFrame`/`observes_readRespect`/
  `accumulator_cleanupFrame` with the recorded-children premise),
  `NestedRegistrationWitness`, `StagingStable`/`StableBase`,
  `divertAdmissible`. Module SHA-256 prefix: `5e2eac3a…` (supersedes the
  `447c2668…` recording — the repair edited Rules.lean).
* `STC.Examples.GlobalRules` (fixture, split into three modules):
  Semantics `1b571c2f…`, Trace `1aa08cf1…`, Evidence `cd66ab99…`. The
  monolithic `GlobalRules.lean` is removed; `Bootstrap.lean` and
  `Examples/Global.lean` import the three.
* Anti-vacuity additions (the re-freeze gate): the four mini-traces
  (success LIFO `[] →[1]→ [2,1] →[3]→ [3,2,1]`; failure with
  `prefixUndo [1]`; landing `[7]` composed onto `[1]` → `[7,1]`; the D48
  guarded coeffect write of key 12), the noncommutativity theorems, and
  the frame discharges. The D48 write guard is fully COMPUTABLE
  (`Multiset.foldr` over the registry entries; zero `noncomputable` or
  `classical` in the fixture).
* Contract attributions recorded for the re-freeze:
  * RECOVERY BOUNDARY: T03 proves inverse source binding, threading, and
    LIFO composition only; the nested-registration inverse is interpreted
    by `RetireInverseAdequate`; arbitrary stage/finish/landing inverse
    observational recovery is MIGRATED to T05B as the relation-indexed
    recovery profile obligation. `stage_inverse` is deleted (rationale in
    `Component.lean`).
  * UNLOAD OWNERSHIP: the recorded-child ownership of foreign unload
    edits is a caller premise of `unload_full_cleanupFrame` and a declared
    component/profile obligation — `LifecycleRule.unload` alone does not
    guarantee the D48 cleanup shape.
* Gates (2026-09-04): `lake build` 3092 jobs zero warnings; the three
  fixture modules compile zero-error zero-warning under `lake env lean
  -DautoImplicit=false -Dpp.unicode.fun=true`; `scan_lean.py STC` exit 1;
  ledger 82/82 PASS; `git diff --check` clean.
* T04 released: `STC.Control.Reachability` / `STC.Control.Episode` keep
  their recorded T04-draft status (compatibility touches only); T04's
  remaining work is per-rule factorization closure, write/read frame-law
  completion, and activation-provenance preservation.

The T03 re-freeze intentionally supersedes the earlier T03 checkpoint; this is
the final T03 freeze, but NOT a T04 completion — per-rule factorization,
write/read frame laws, and activation-provenance preservation must close before
T05 theorem lanes can rely on these signatures.
