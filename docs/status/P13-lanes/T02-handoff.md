# P13-T02 Lane Handoff

* Scope: `STC/State/Component.lean`, `Fiber.lean`, `Global.lean`,
  `Global/Observation.lean`, and `Examples/GlobalModel.lean`.
* Result: T02 positive production state and model API freeze, closed.
* Evidence: `I K E` at the carrier level. The carrier is positive/data-only;
  D43-D50/D58 surfaces are defined and checked; the D32 representation
  theorems and the D33 lifted-state relation are proved; semantic rule
  reachability remains T03+.

## Freeze checkpoint

* Freeze record: `docs/status/P13-api-freeze.md` T02 checkpoint (central owner).
* Base: `8ae8ab5` (T01C close) on `codex/p13-continuation`;
  checkpoint commit: `db9d180`.
* Cross-lane compatibility touches (recorded, minimal, required by the
  `FiberCell.committedView` field addition): `STC/Examples/GlobalRules.lean`
  (`cell0` gains `committedView := ∅`) and `STC/Control/Reachability.lean`
  (`RelatedCell` compares committed provider views through the growing
  bijection; `sameResolved_implies_sameInputs` conjunct count updated).
  These lanes reopen their own handoffs when they open.
* Dropped unfrozen draft names: `ProviderModel` (replaced by executable
  `providersOf` plus proved soundness/completeness/uniqueness), placeholder
  `TargetView` (replaced by per-fiber `targetView`/`targetProviders`),
  `toPositiveContext` (universe-blocked, see below). The previous
  P13-api-freeze inventory explicitly stated the final T02/T03/T04 freeze
  remained open; this checkpoint closes the T02 window.

## T01C frozen-interface limitations (recorded, no reopen)

* `PositiveContext` shares one universe between its ambient and code
  parameters, which the mixed-universe concrete carriers cannot instantiate;
  the D32 representation is delivered at the `PositiveRegistry` level
  (`toPositiveRegistry` + `toPositive_keys` + the three lookup theorems).
  Smallest upstream change if ever reopened: split `Code` into its own
  universe.
* `ObservationKit` shares universes between registry/name and edit/life
  carriers; the concrete D33 kit assembly (`observationKit`,
  `stateObs_eq_lifted`) is therefore uniform-universe, while the
  mixed-universe component instantiations `registryObservation` and
  `committedObservation` are kept.

## Public API inventory (frozen)

* `STC.State.Fiber`: `LifecyclePhase`, `CommittedData`, `FiberPayload`,
  `FiberCell` (now with `committedView : Finmap (fun _ : Key => Name)`, the
  paper's `ω_n`), `InitiallyInactive`, `initiallyInactive_decidable`.
* `STC.State.Global`:
  * carrier: `GlobalState`, `Fiber`, `issuedInOrder`, `activeNames`,
    `ActiveStoreView`, `activeStore`, `stableImage`;
  * updates/frames: `updateFiber` + `_lookup_eq/_lookup_ne/_keys/_history/
    _ledger/_coeffects`, `WriteFrame`, `ReadNoninterference`,
    `updateFiber_writeFrame`, `updateFiber_readNoninterference`;
  * D47: `allocate` + `_lookup_fresh/_lookup_ne/_keys/_history/_ledger/
    _coeffects/_ambient`, `nextBirth`, `retire?` + `_none_iff/_some_iff/
    _retired`;
  * D45: `ProvidesNow`, `providersOf` + `_sound/_complete/_unique/
    _card_le_one`;
  * D46: `targetProviders`, `targetSatisfied`, `targetSatisfied_iff`,
    `targetView` + `_isSome_iff/_some_iff/_mem/_provides`;
  * D49: `Installed`, `Failed`, `PendingFlight`, `Quiescent`;
  * D50: `ReliedUpon`, `reliedUpon_iff_view`;
  * D58: `ParentStep`, `ParentClosed`, `ParentAcyclic`, `TableConfined`,
    `ProvisionDisjoint`, `CommittedViewClosed`, `CommittedProvidersClosed`,
    `WellFormedProfile` (lifecycleCoherent/root/declarations),
    `WellFormed` + nine `wellFormed_*` projections;
  * D32: `FiberData`, `FiberCode`, `fiberData`, `fiberCode`, `toPositiveCell`,
    `toPositiveEntries` + `_keys/_nodupKeys`, `toPositiveRegistry` +
    `_entries/_keys`, `PositiveCellObs`, `toPositive_lookup_some`,
    `toPositive_lookup_none`, `toPositive_lookup_isSome_iff`;
  * profiles: `AlphaCodeProfile`, `NameNeutral`, `FactorizationProfile`,
    `ProgressProfile`, `ConfluenceProfile`.
* `STC.State.Global.Observation`: `GlobalObservation`, `StateObs` +
  `_registry/_coeffects/_lifecycle/_controlEdit/_names/_refl/_symm/_trans`,
  `registryObservation`, `committedObservation`, `observationKit`,
  `stateObs_eq_lifted`.

## Evidence

* `K`: `providersOf_sound/complete/unique/card_le_one` (unique/card consume
  WellFormed-provisionDisjoint), `targetSatisfied_iff`, `targetView_*`,
  `toPositive_keys` + the three lookup theorems (D32 representation),
  `StateObs` closure laws + `stateObs_eq_lifted` (D33 instantiates the T01C
  `ObservationKit`/`liftedStateObs`).
* `E` (`STC/Examples/GlobalModel.lean`): two fibers (provider `1` providing
  `{10}`, nested consumer `2` requiring `{10}`, parent `some 1`), ordered
  allocation history `[1,2]`, `providersOf` selection, `targetView 2 =
  some {1}`, quiescence, `WriteFrame`/`ReadNoninterference` instances,
  `ReliedUpon 2 1`, full `WellFormed` proof split into per-invariant lemmas
  (`model_parentClosed/_parentAcyclic/_tableConfined/_provisionDisjoint/
  _committedViewClosed/_committedProvidersClosed`) and assembled,
  positive representation keys and lookup correspondence, `StateObs`
  reflexivity and kit equivalence, `NameNeutral` Unit codes, and a
  nonconstant `FactorizationProfile` witness (`empty` vs `state1`).

## Proposed ledger deltas (central integration, not applied here)

* D32 → `completed/proved` (representation theorems; carrier-level evidence).
* D33 → `completed/proved` (concrete kit + closure laws).
* D43 → `completed/proved` at the carrier/interpretation-contract level
  (D48 write/read frames now live separately in Global.lean).
* D44, D45, D46, D49, D50 → `completed/proved` at the carrier level
  (rule-confinement/concrete transition proofs remain T03/T05A).
* D47, D48, D58 → `in_progress/aligned`; D47 transition theorem and D48
  concrete rule-confinement stay with T03, D58 preservation (T59) with T05A.

## Gates (actual, 2026-09-01)

* Focused: `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true` on each
  of `STC/State/Fiber.lean`, `STC/State/Global.lean`,
  `STC/State/Global/Observation.lean`, `STC/Examples/GlobalModel.lean`,
  `STC/Examples/GlobalRules.lean`, `STC/Control/Reachability.lean`:
  exit 0, zero warnings.
* Full build: `lake build` completed successfully (3090 jobs, exit 0).
* `python scripts/scan_lean.py STC`: exit 1 (clean).
* `python scripts/validate_definition_ledger.py
  docs/status/Definition-Ledger.json`: 82/82, both frozen H03/H04 hashes OK.
* Forbidden-token scan (`sorry|admit|axiom|unsafe`) over the P13 production
  and example paths: exit 1 (no matches).
* Import-boundary scan (production imports of examples/conformance/spikes):
  exit 1 (no matches).
* `git diff --check`: clean.
* Protected-path diffs (merged APIs, examples, blueprints, P8 manifest):
  clean; only T02-owned modules plus the two recorded compatibility touches
  changed.
