# P13-T02R Lane Handoff (semantic-view/profile repair)

* Scope: `STC/State/Component.lean`, `STC/State/Global.lean`,
  `STC/Examples/GlobalModel.lean`.
* Authority: lead ruling (2026-09-01) inserting a repair between the T02
  freeze and T03. No new ADR; no `FiberCell`/`GlobalState` carrier fields
  changed. T03 rebases onto this checkpoint before implementing the
  authoritative inductive rules.
* Result: T02R closed and re-frozen. The repair keeps a legal `O-Retire`
  and a legal `L-Leave` from breaking a dependent's committed binding or
  `WellFormed`, and replaces the `Option (Finset Name)` target view with
  the precise `TargetViewAt`/`TargetAbsent` machinery the rules consume.

## Freeze checkpoint

* Freeze record: `docs/status/P13-api-freeze.md` T02R checkpoint.
* Base: `c247991` (T02 freeze + docs) on `codex/p13-continuation`;
  checkpoint commit: `61a0040`.
* Superseded T02 surface (recorded reopen, lead decision): the old
  `ProvidesNow` (declared provides, active ∧ ¬retired), the old
  `Quiescent` (mid-transition exclusion only), the old `Installed`
  (= lookup-definedness), the old `ReliedUpon`, the old nine-conjunct
  `WellFormed`, and the flat `ComponentSemantics.iterator` field.
* Cross-lane compatibility touches: none. `STC/Control/Reachability.lean`
  and `STC/Control/Episode.lean` (open T04 drafts) use none of the
  redefined names; they will need recorded label-shape edits at T03.

## Public API inventory (frozen at this checkpoint)

* `STC.State.Component`:
  * `StageResult State Iterator Accumulator Failure` with `yield` (after,
    yielded inverse, continuation), `halt` (after, final inverse), `raise`
    (before-state, failure), plus projections `state`/`inverse?`/`failure?`.
  * `ComponentSemantics`: `action`; `stage` (replaces the removed
    `iterator` field); `composeInverse`; `identityAccumulator`; `launch`;
    `flight` (landing execution); `failure`; `undo`; `observes`;
    `writesWithinProvision`; `continuationStable`; `rank`;
    `accumulatorFrame` (abstract relation field, to be instantiated by T03
    with the unload-time cleanup frame); laws `noWriteOutside`,
    `action_frame`, `stage_frame`, `inverse_law`, `stage_inverse`,
    `relation_respect`, `rank_law` (stage-form), `continuation_stable`,
    `flight_frame`, `failure_frame`, `composeInverse_law`,
    `identityAccumulator_law`, `accumulator_frame`.
* `STC.State.Global`:
  * D45: `ProvidesNow` = active ∧ key ∈ committed table (retirement does
    not stop a binding); `CommittedProvides` = active/unloading ∧ key ∈
    committed table (teardown views); `providersOf` (table-based,
    executable) with re-proved `_sound`/`_complete` and
    `providersOf_unique`/`_card_le_one` (now consuming
    `wellFormed_tableConfined`).
  * D46: `TargetViewAt state owner ω` (domain = requires exactly, every
    entry a current `ProvidesNow` provider), `TargetAbsent`;
    `targetView`/`targetProviders`/`targetSatisfied` retained as finite
    executable projections, no longer rule inputs.
  * D49: `Registered` (lookup-defined) vs `Installed` (phase ∈
    reloading/active/unloading), `installed_registered`; `Failed`,
    `PendingFlight` unchanged.
  * D50: `ReliedUpon` = dependent ≠ provider ∧ dependent installed ∧
    ∃ required key with a committed-view entry naming the provider;
    `reliedUpon_iff_view` updated.
  * Quiescence: `Quiescent` = no reloading/unloading, no pending flight,
    and every active fiber's committed view equals its exact current
    target.
  * D48 split: `WriteFrame`, `ReadNoninterference` (selected-body static
    frame, unchanged) plus new `ReadRespect` (two-run required-read
    equality), `RegistrationFrame` (registry/ledger grow only at fresh,
    history appends, stores fixed), `CleanupFrame` (owner-cell edits plus
    retire?-shaped recorded child-retirement inverses; ledger/history/
    coeffects fixed); theorems `updateFiber_readRespect`,
    `updateFiber_cleanupFrame`, `retire?_cleanupFrame`,
    `allocate_registrationFrame`.
  * D58: new conditions `ActiveTableCoherent` (active cells' committed
    tables folded into the coeffect-store domain), `CommittedViewDomain`
    (view keys ⊆ declared requires), `IncarnationCoherent` (cell
    incarnation = registry key), `AllocationCoherent` (history nodup;
    birth index points at own name), `LedgerCoherent` (registry and
    history ⊆ everIssued), bundled as `DataCoherent`; `WellFormed` is ten
    visibly separate conjuncts with the nine retained projections plus
    `wellFormed_activeTableCoherent`/`_committedViewDomain`/
    `_incarnationCoherent`/`_allocationCoherent`/`_ledgerCoherent`.
  * `activeNames`/`activeStore`/`stableImage`: retired check dropped
    (retirement alone does not leave the active set).
* `STC.Examples.GlobalModel`: fixture updated to the new semantics —
  provider cell gains a committed `{10 ↦ 0}` table and the ambient
  coeffect store holds `{10}`; all ten `WellFormed` conjuncts proved
  separately; `Quiescent` proved with target alignment; teardown
  `CommittedProvides` witness proved; `ReliedUpon` proved with the new
  envelope.

## Evidence

* `K`: `providersOf_sound/complete/unique/card_le_one` (re-proved over
  table-based selection), `installed_registered`, `allocate_registrationFrame`,
  `updateFiber_readRespect`, `updateFiber_cleanupFrame`, `retire?_cleanupFrame`,
  the retained update/allocate frame laws, the re-proved
  `targetSatisfied_iff`/`targetView_*` family.
* `E` (`STC/Examples/GlobalModel.lean`): the two-fiber provider/consumer
  fixture under the repaired relations, including the ten-way
  `WellFormed` split, quiescent target alignment, and teardown-provider
  evidence.
* `ComponentSemantics` laws remain profile-level premises: no concrete
  instantiation exists yet (first instantiations arrive with the T03
  fixture).

## Recorded readings (freeze notes)

* "active-table fold/coherence" is read as `ActiveTableCoherent`: the
  committed tables of active cells are folded into the ambient coeffect
  store domain (committed keys are present in the store).
* "recorded child-retirement inverse" is read at carrier level as
  `retire?`-shaped edits: `CleanupFrame` permits non-owner cells to flip
  their retired flag from false to true, nothing else.
* "two-run read-respect" is read as `ReadRespect`: across two executions,
  the owner's required keys read equal values.

## Proposed ledger deltas (central integration, not applied here)

* None. Rows D43–D50/D58 remain T02-owned; the repair strengthens the
  carrier-level semantic views without changing row dispositions.

## Gates (actual, 2026-09-01)

* Focused: `lake env lean -DautoImplicit=false -Dpp.unicode.fun=true` on
  each of `STC/State/Component.lean`, `STC/State/Global.lean`,
  `STC/Examples/GlobalModel.lean`: exit 0, zero warnings.
* Full build: `lake build` completed successfully (737 targets, exit 0),
  including the untouched T03/T04 drafts on top of the repaired state.
* `python scripts/scan_lean.py STC`: exit 1 (clean).
* `python scripts/validate_definition_ledger.py
  docs/status/Definition-Ledger.json`: 82/82, both frozen H03/H04 hashes OK.
* Forbidden-token scan (`sorry|admit|axiom|unsafe`) over the three touched
  files: exit 1 (no matches).
* Import-boundary scan over the touched production files: exit 1 (no
  matches).
* `git diff --check`: clean. Changed-path allowlist: exactly the three
  lane-owned files.
