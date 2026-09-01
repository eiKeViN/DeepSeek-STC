# P13 API Freeze

| Field | Value |
|---|---|
| Plan | `DH-P13-GLOBAL-METATHEORY-EXEC-01` |
| Base | `96b8752` (`P13 plan added`) |
| Freeze state | T02 + T02R checkpoints recorded; T03/T04 checkpoints remain open |
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

No frozen upstream file was edited. This inventory is not the final semantic
freeze: per-rule factorization, write/read frame laws, and activation-provenance
preservation must close before T05 theorem lanes can rely on these signatures.
