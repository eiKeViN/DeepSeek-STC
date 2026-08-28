# P5 handoff report: abstract state, registry, and observation layer

| Field | Value |
|---|---|
| Plan | `DH-P5-EXEC-01` (`docs/plans/P5-Execution-Plan.md`) |
| Wave | P5 — abstract state, observation, registry, and ADR-03 state seam |
| Repository | `https://github.com/eiKeViN/DeepSeek-STC` |
| Teammate-plan baseline | `9969ec5114ce0d94887f540e67b4581ff560ae1d` |
| Plan integration commit | `2a5214950852ebe6d459b4c1bf39d21520698426` |
| Branch-alignment merge | `c20ca6a` |
| Latest main sync | `0971772`; merged as `bcd65a2` |
| Branch | `codex/p5-state-registry` |
| Final implementation commit | `bcd65a2` |
| Handoff commit | The commit containing this report |
| PR target | `main` |
| Namespace | `STC`; P5 state seam under `STC.State.FinmapAdapter` |
| Merge status | Not merged; no automatic merge performed |

## 1. Authority and provenance

The branch was realigned to `origin/main` after the teammate plan landed. Its
initial effective P5 base was `2a52149`, whose parent `9969ec5` contains the
merged P1/P2 implementation assumed by the plan. Before PR handoff, main
advanced to `0971772`; merge `bcd65a2` incorporated its module-format migration
and converted all P5 files to the same module/public-import conventions. P5
does not import P3 or P4 modules and remains independently buildable.

The following boundaries were preserved:

- frozen Formal Reference, H03, H04, and accepted ADR artifacts are unchanged;
- historical Lean spikes are neither modified nor imported;
- P1 `Relation`/`Result` and P2 `Effect` APIs are unchanged;
- `STC.Adapter` remains untouched for the later runtime-side abstraction seam;
- no concrete Cordis declaration or runtime behavior enters the metatheory.

## 2. COMPLETED_NOW

### P5-T01 — abstract state and observation profiles

`STC/State/Like.lean` provides the small `StateLike` projection and
`ObservationProfile`. A supplied state relation must be accompanied by
`project_respects`; `ObservationProfile.exact` constructs the canonical exact
pullback profile.

`STC/State/Observation.lean` provides distinct `CoreStateObs`, `LifecycleObs`,
`EraseControl`, and `NameAwareObs` relations. No global `Setoid`, automatic
profile refinement, or behavior-erasing common equality is installed.
`StoreRegistryBoundary` records only a one-way observation-respecting active
store projection; it does not equate registry and coeffect domains.

### P5-T02 — RegistryLike and Toy registry

`STC/State/RegistryLike.lean` provides a finite uniform registry interface with:

- `empty`, `lookup`, raw overwrite `insert`, absent-key-no-op `erase`, and a
  `List` domain;
- a `Nodup` domain certificate;
- empty, same-key, distinct-key frame, and membership/lookup laws;
- pointwise, tag-strict `RegistryObs` rather than carrier equality;
- checked `insertFresh?` and `erasePresent?` policy wrappers;
- observational recovery after fresh insert/erase and captured erase/reinsert.

`STC/State/Toy.lean` implements the interface with an executable
association-list plus `Nodup` representation. It exercises three keys, two
values, raw overwrite, fresh acceptance, duplicate rejection, erasure, and a
deliberately duplicate candidate that cannot satisfy the carrier invariant.

### P5-T03 — ADR-03 state-side seam

`STC/State/FinmapAdapter.lean` provides the planned one-way R0 interface:

- positive `RawState` with ambient data and an abstract registry carrier;
- seven separately visible `CoreWFSpec` obligations;
- separate root/declaration `BoundaryWFSpec` obligations;
- `CoreWellFormed`, `WellFormed`, and proof-carrying `ValidState`;
- sound, complete, and unique `ProviderProvenance` fields;
- the static-only `checkedUpdate` gate and exact success/failure equations;
- one-way `StateAbstraction` observation evidence.

These are interfaces and admission obligations. No concrete provider adequacy,
well-formedness preservation, transition semantics, or runtime refinement is
claimed.

### P5-T04 — ADR-02 dependent coeffect façade

`STC/State/CoeffectStore.lean` preserves the authoritative dependent Mathlib
`Finmap` architecture. It exposes `Store`, lookup, keys, insert, erase,
pointwise dependent `StoreObs`, and lookup/domain/frame laws. The finite fixture
uses a genuinely dependent family with `Nat` at one key and `Bool` at another.

The façade is not the uniform fiber registry and is not a mutable root/global
cache. Full ADR-02 extract/union/extensionality, support-update/recovery,
distinct-key algebra, disjoint-union, binding, notification, and partial-effect
surfaces remain deferred.

## 3. Checked theorem inventory

All theorems below are `INDEPENDENT_NOW`; no P2/P3/P4 preservation statement
was fabricated.

- Observation: `ObservationProfile.exact_stateRel`, `pullback_comp`,
  `lifecycleObs_iff`, the three lifecycle projections, `nameAwareObs_iff`, and
  the two name-aware projections.
- Registry: `registryObs_lookup`, `registryObs_same_domain`,
  `registryObs_insert`, `registryObs_erase`, `domain_insert_iff`,
  `domain_erase_iff`, the checked-wrapper failure/success equations, and the two
  observational recovery theorems.
- Toy: list lookup/erase/insert, subset, uniqueness, domain, frame, and concrete
  instance proof fields; `toyExampleChecks_expected` pins the finite result.
- Coeffect store: empty lookup, key-membership/definedness, insert/erase same-key
  and frame laws, `storeObs_lookup`, and `coeffectStoreObs_same_keys`.
- ADR-03 seam: `checkedUpdate_eq_some_iff` and
  `checkedUpdate_eq_none_iff`; neither theorem claims WF preservation.
- Finite examples: `lifecycle_not_nameAware`,
  `eraseControl_not_lifecycle`, and `stateReport_expected`.

No theorem relates `EraseControl` and `LifecycleObs` in either direction.

## 4. Executable evidence

The standalone Toy theorem pins the following elaboration-time result:

```text
[true, true, true, true]
```

The final `STC/Examples/State.lean` theorem pins the following computed report:

```text
{ emptyLookup := none,
  insertLookup := some (STC.ToyValue.first),
  distinctLookupFramed := true,
  rawOverwriteUpdated := true,
  rawOverwriteDomainNodup := true,
  duplicateFreshInsertRejected := true,
  freshInsertAccepted := true,
  lawBreakingCandidateRejected := true,
  missingLookup := none,
  missingEraseRejected := true,
  presentEraseCapturedValue := true,
  presentEraseRemovedKey := true,
  freshInsertEraseRecovered := true,
  capturedEraseInsertRecovered := true,
  lifecycleRelatedButNameAwareRejected := true,
  eraseControlRelatedButLifecycleRejected := true,
  dependentCoeffectNatLookup := some 7,
  dependentCoeffectBoolLookup := some true,
  checkedUpdateAccepted := true,
  checkedUpdateRejected := true }
```

The report is pinned by `stateReport_expected`; the observation-profile
separation statements are also proved directly as Props.

## 5. Definition Ledger evidence

Only derived fields were edited. Dependency lists, treatments, paper anchors,
H03/H04 fields, and frozen readiness remain unchanged.

| Row | Delivery | Evidence | P5 interpretation |
|---|---|---|---|
| D22 | `in_progress` | `proved` | dependent façade and delivered laws; full ADR-02 theorem surface deferred |
| D32 | `in_progress` | `seam_only` | abstract state and Raw/ValidState R0 contracts |
| D33 | `in_progress` | `proved` | explicit pullback/profile/store observations; operation-induced equivalence deferred |
| D44 | `in_progress` | `aligned` | uniform registry shell/Toy only, not concrete FiberCell lifecycle |
| D45 | `in_progress` | `seam_only` | registry laws and provider contract, not active-union adequacy |
| D53 | `planned` | `aligned` | observation names/boundaries only; trace/alpha work remains later |
| D58 | `in_progress` | `seam_only` | explicit WF contract without transition-preservation proof |

D46 and D47 remain `planned`/`pending`. No blocked-decision row was promoted
merely because an interface compiled.

## 6. STAGED_FOR_P2_P3_P4

The following obligations remain unstated in production P5:

- operation/effect/partial-operation preservation of `ValidState`;
- iterator preservation and lifecycle-step congruence;
- provider-changing transition preservation and active-store completeness;
- partial failure, ranked iteration, and prefix-undo semantics;
- the complete ADR-02 operation and independence theorem surfaces.

Each requires actual merged semantics and explicit preservation hypotheses.

## 7. DEFERRED_TO_P6_OR_LATER

- alpha actions, permutation transport, and name-bearing trace/reference laws;
- freshness-ledger and orchestration-boundary semantics;
- concrete FiberCell, lifecycle, provider, and active-union instances;
- the P7 two-counter vertical slice and P8 runtime refinement;
- all R1+ evidence and Cordis implementation correspondence.

P5 retains a name-aware view and does not bake alpha equivalence into raw
execution equality.

## 8. BLOCKED and module-format integration

No semantic P5 obligation in the independently executable scope is blocked.

The earlier `FORMAT-DEVIATION-P5-01` was resolved by main commit `133b7da`,
which migrated the Foundation/P2 import closure to Lean 4.33 modules. Merge
`bcd65a2` adopted that lead-owned migration and converted every P5 production
file to `module`, sorted `public import`s, and `@[expose] public section`.

Main also prohibited top-level `#eval` in exposed library modules. P5 now pins
all finite results with `example`/theorem proofs using `by decide`; no library
module relies on native shared-library evaluation.

## 9. Validation evidence

Every focused command used the required explicit Lean options and completed
with zero errors and zero warnings:

```text
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Like.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Observation.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/RegistryLike.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Toy.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/CoeffectStore.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/FinmapAdapter.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/State.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
```

Final integration gates:

```text
$ lake build
Build completed successfully (738 jobs).
exit 0

$ python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
Definition-Ledger validation: PASS
  82/82 covered; duplicates 0; unknown 0
  H03 source hash OK: 8f99db87d7aa4d85...
  H04 source hash OK: 63d1fb68bcebb63e...
  no inferred transitive readiness
exit 0

$ python scripts/scan_lean.py STC
<empty output>
exit 1 (clean by the scanner contract)

$ git diff --check origin/main..HEAD
<empty output>
exit 0

$ git status --short --branch
## codex/p5-state-registry
exit 0
```

The exact scanner stdout/stderr is preserved as the zero-byte
`docs/status/P5-scan-raw.txt` artifact.

## 10. Independent review

The first fresh GPT-5.6 Sol review returned `PASS_WITH_FIXES`. It found no
semantic or proof-integrity blocker. Its sole substantive finding was that D22
had been marked completed even though the full ADR-02 theorem surface is
deferred. Commit `4d4eb3e` made the missing surface explicit and tightened
`RawState` documentation so the generic registry parameter is not described as
intrinsically finite.

A second fresh review caught a mechanical Ledger edit error: that first fix had
changed D1 instead of D22. Commit `2bf1ae0` restored D1 to
`completed`/`tested` and set D22 to `in_progress`/`proved`. The validator,
build, scanner, and diff checks all passed again after the exact correction.

The reviewers independently confirmed observer non-vacuity, registry laws,
Toy correctness, store/registry separation, honest R0 claim strength, P3/P4
independence, P6 compatibility, standard proof axioms only, and all validation
gates. Their final pre-sync verdict was `PASS`.

Post-main-sync fresh re-review verdict: **PENDING**.

## 11. PR handoff

PR #5 targets `main` from `codex/p5-state-registry`. After the post-main-sync
fresh review returns `PASS`, push the conflict-resolution merge and updated
handoff. Stop before merge; no merge is automatic.
