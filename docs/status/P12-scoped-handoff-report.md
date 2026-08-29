# P12 Handoff Report: Scoped Coeffect Integration

| Field | Value |
|---|---|
| Plan | `DH-P12-SCOPED-EXEC-01` (`docs/plans/P12-Scoped-Execution-Plan.md`) |
| Wave | P12 — scoped coeffects |
| Branch | `codex/p12-scoped-execution` |
| Base | `69b4184` (post-planning commit, origin/main) |
| Date | 2026-08-29 |
| Toolchain | Lean 4.33.0 / Mathlib v4.33.0 |
| Gate | ADR-10 accepted status record verified at baseline (`record_status=accepted`, `architecture_status=closed`, `formal_acceptance=true`) |

## Task status

| Task | Result |
|---|---|
| T01 | RealmModel + RealmRef: typed transport via `key_eq` witnesses only; `cast_castInv`/`castInv_cast` round-trips; `ext`; finite toy with two logical keys and two realms (`depA`/`depB`) under one key |
| T02 | `ResolverSpec` (relational) kept distinct from executable `Resolver` (finite support); concrete `resolverUpdate` with hit/miss/support/idem/satisfaction laws; abstract `ResolverUpdate` interface + `defaultResolverUpdate` instance |
| T03 | `RealmStoreOps` interface instantiated at the authoritative P5 store (`RealmStore M := Coeffect.Store (fun r => V (M.keyOf r))`); scoped ops + self/frame/two-resolver frame laws; captured-reference inverses with `Finmap`-level restoration proofs |
| T04 | `MetaAlgebra`/`MetadataPrecedence` split; `InterceptionSpec` presence/support laws; `ScopedContext` + `deriveIsolate`/`deriveIntercept` persistence and precedence laws; `ProviderAdapter`/`effectiveMeta`/`provideWith` boundary |
| T05 | `FlatEmbedding` with the three ADR-10 commuting diagrams; `FlatImage` stability laws; no converse/projection/surjectivity defined |
| T06 | Finite deterministic evidence incl. same-key/different-realm frame case and pinned report `scopedReport_expected := by decide` |

## File and import graph

```text
STC.Scoped.Model            (imports: —)
        ↓
STC.Scoped.Resolver        (imports: Mathlib.Data.Finset.Basic, STC.Scoped.Model)
        ↓
STC.Scoped.Store           (imports: STC.Scoped.Resolver, STC.State.CoeffectStore)
        ↓
STC.Scoped.Context         (imports: STC.Scoped.Store)
        ↓
STC.Scoped.Flat            (imports: STC.Scoped.Context)
        ↓
STC.Scoped                 (public umbrella; imports Context, Flat, Model, Resolver, Store)
        ↓ (evidence only, never imported by production)
STC.Examples.Scoped        (imports: STC.Scoped)
```

No Control, Staging, or Support dependency. No historical spike import.
No module outside the P12 ownership list was edited.

## Public declaration inventory

* `STC/Scoped/Model.lean` — `RealmModel`, `RealmRef`, `RealmRef.cast`,
  `RealmRef.castInv`, `RealmRef.defaultRef`, `RealmRef.ext`,
  `RealmRef.cast_castInv`, `RealmRef.castInv_cast`, `RealmRef.defaultRef_token`,
  `RealmRef.cast_defaultRef`, `RealmRef.castInv_defaultRef`, `ToyKey`,
  `ToyValue`, `ToyRealm`, `toyModel`, `toyDepARef`, `toyDepBRef`,
  `toy_same_key_realms_distinct`, `toy_keys_distinct`, `toy_value_dep`
* `STC/Scoped/Resolver.lean` — `ResolverSpec`, `Resolver`, `ResolverSatisfies`,
  `ResolverTypePreserving`, `resolver_type_preserving`, `defaultResolver`,
  `resolverSatisfies_default`, `resolverUpdate`, `resolverUpdate_hit`,
  `resolverUpdate_miss`, `resolverUpdate_support_subset`,
  `resolverUpdate_idem_resolve`, `resolverUpdate_idem_overrideKeys`,
  `resolverUpdate_idem`, `resolverUpdate_satisfies`, `ResolverUpdate`,
  `defaultResolverUpdate`
* `STC/Scoped/Store.lean` — `RealmStoreOps`, `scopedLookup`, `scopedInsert`,
  `scopedErase`, `scopedLookup_empty`, `scopedLookup_insert_self`,
  `scopedLookup_erase_self`, `PhysicalDistinct`, `physicalDistinct_iff`,
  `physicalDistinct_symm`, `physicalDistinct_of_ne`, `scopedLookup_insert_frame`,
  `scopedLookup_erase_frame`, `scopedLookup_insert_erase_self`,
  `scopedLookup_insert_frame_twoResolvers`, `scopedLookup_erase_frame_twoResolvers`,
  `RealmStore`, `finmapRealmStoreOps`, `ScopedInsertInverse`,
  `scopedInsertInverse`, `scopedInsertInverse_undo_eq`, `ScopedEraseInverse`,
  `scopedEraseInverse`, `scopedEraseInverse_restored_eq_lookup`,
  `finmap_scopedInsertInverse_restores_lookup`,
  `finmap_scopedInsertInverse_restores`,
  `finmap_scopedEraseInverse_restores_lookup`,
  `finmap_scopedEraseInverse_restores`
* `STC/Scoped/Context.lean` — `MetaAlgebra`, `MetadataPrecedence`,
  `InterceptionSpec`, `interceptionSpec_support_iff`, `ScopedContext`,
  `deriveIsolate`, `deriveIntercept`, `deriveIsolate_persistent`,
  `deriveIsolate_resolver_hit`, `deriveIsolate_resolver_miss`,
  `deriveIsolate_support_bound`, `deriveIntercept_persistent`,
  `deriveIntercept_merge_present`, `deriveIntercept_merge_absent`,
  `scopedContext_insert_frame`, `ProviderAdapter`, `effectiveMeta`,
  `effectiveMeta_context_precedence`, `provideWith`,
  `provideWith_context_precedence`, `provideWith_neutral_context`,
  `provideWith_key_local`
* `STC/Scoped/Flat.lean` — `FlatEmbedding`, `FlatImage`, `flatImage_self`,
  `flatImage_scopedInsert`, `flatImage_scopedErase`, `flatImage_lookup`,
  `flatEmbedding_lookup_insert`, `flatEmbedding_lookup_erase`
* `STC/Examples/Scoped.lean` — `depBResolver`, `depARef`, `depBRef`,
  `overriddenCacheRef`, `overriddenCacheRef_is_default`,
  `depBResolver_satisfies_defaultSpec`, `toyOps`, `toyStore0`, `toyStore1`,
  `toyMeta`, `neutralToyMeta`, `toyMetaAlg`, `toyMetaPresent`,
  `toyMetaPrecedence`, `depInterception`, `toyContext`,
  `toyResolverUpdateOps`, `isolatedContext`, `toyAdapter`, `toyFlatModel`,
  `ToyFlatStore`, `toyFlatOps`, `toyFlatEmbedding`, `flatStore0`,
  `flatStore1`, `toyTokenEq`, `ScopedReport`, `scopedReport`,
  `expectedScopedReport`, `scopedReport_expected`

## P5 adapter representation

`RealmStore M := STC.Coeffect.Store (fun r : M.Realm => V (M.keyOf r))` — the
authoritative ADR-02 dependent `Finmap` façade at the physical realm token
type. `finmapRealmStoreOps` proves the five `RealmStoreOps` laws from the P5
lemmas `coeffect_lookup_empty/insert/insert_ne/erase/erase_ne`; the rollback
laws use `Finmap.ext_lookup`. No second store, no change to the P5
representation, no realm push into core state.

## Assumptions made explicit

* Executable resolution requires `[DecidableEq K]`; `resolverUpdate`
  additionally requires `[DecidableEq M.Realm]` (token comparison decides
  whether the override support must grow). Both appear in signatures.
* Frame laws take `PhysicalDistinct` (inequality of the selected physical
  tokens) as an explicit premise. `physicalDistinct_of_ne` shows logical
  inequality implies it; the ADR aliasing caveat (the converse may fail) is
  documented on the declaration.
* Insert-undo restoration assumes the selected realm was absent before the
  insert (the paper `set(k,v)` precondition); erase-undo assumes the binding
  was present. Both are explicit premises of the `Finmap`-level laws.
* Right-biased metadata override is the `MetadataPrecedence.right_wins` field,
  never inferred from monoid laws; presence (`support`) is separate from the
  `Option` payload.
* `FlatEmbedding` laws are generic over any `RealmStoreOps`/`Resolver`; the
  ADR flat conditions (identity resolver, no aliasing, neutral interception
  metadata) are ambient conditions of the toy instance and are documented in
  `STC/Scoped/Flat.lean`. No flatten converse exists.

## Evidence classification

| Family | Evidence | Notes |
|---|---|---|
| Typed realm model + transport | `A I K E` | round-trip and `ext` theorems; toy with two realms under one key |
| Resolver split + updates | `A I K E` | satisfaction bridge checked; hit/miss/support/idem laws |
| Scoped store ops + frame laws | `A I K E` | incl. two-resolver same-key/different-realm frame case |
| Captured inverses / rollback | `K` | restoration proved pointwise at the `Finmap` level; capture is by construction (`rfl`-checked fields) |
| Metadata / interception / contexts | `A I K E` | persistence, precedence, neutrality, key-locality |
| Flat embedding | `A I K E` | three diagrams + image stability; one-way only |
| Finite executable report | `E` | `scopedReport_expected : scopedReport = expectedScopedReport := by decide` |

Not claimed: Cordis runtime, Section-4 realm-aware metatheory, R1+
refinement, D27/D74 discharge, provider uniqueness, active-store fold,
lifecycle `WellFormed` preservation (all remain deferred per ADR-10 scope).

## Finite example inventory (T06)

1. default realm resolution (`depARef.token = .depA`);
2. resolver override hit (`depB`) and miss (`cache`) behavior, incl. the
   checked `resolverUpdate_hit`/`resolverUpdate_miss` invocations and finite
   support membership;
3. two realms under one logical key remain physically distinct
   (`depARef.token ≠ depBRef.token`);
4. scoped insert, lookup, erase over the P5 store; frame case for two keys and
   the two-resolver same-key frame case; captured inverse restorations;
5. metadata precedence under interception (`contextMeta .dep = some 5`,
   absent key unchanged);
6. persistent `deriveIsolate`/`deriveIntercept` behavior (hit/miss/persistence
   laws);
7. flat embedding on values inside its image (`embed := id` under the identity
   model; lookups pinned by `decide`; derived diagrams; `FlatImage` checks).

## Proposed Definition Ledger deltas (central integration, not applied here)

Convention used: `completed`/`proved` for rows this lane discharged;
`planned` + explicit `deferred_reason` for dependency-blocked rows, until the
repository adopts a global normalization rule.

| Row | Current | Proposed | Delivery vocabulary | Lean symbols (module) | Evidence | Theorem strength | Remaining `deferred_reason` |
|---|---|---|---|---|---|---|---|
| D28 | planned/pending | completed/proved | `completed`, `proved` | `RealmModel`, `RealmRef`, `Resolver`, `ResolverSpec`, `ResolverSatisfies`, `resolverUpdate`, `ResolverUpdate` (`STC/Scoped/Model.lean`, `STC/Scoped/Resolver.lean`) | A I K E | total type-preserving resolver; finite support; update hit/miss/support/idem; satisfaction bridge | provider uniqueness, active-store fold, lifecycle WF preservation deferred (ADR-10) |
| D29 | planned/pending | completed/proved | `completed`, `proved` | `scopedLookup`, `scopedInsert`, `scopedErase`, frame laws, `ScopedInsertInverse`, `ScopedEraseInverse`, `finmap_*_restores` (`STC/Scoped/Store.lean`), `deriveIsolate` laws (`STC/Scoped/Context.lean`) | A I K E | lookup/insert/erase self laws; PhysicalDistinct frame laws incl. same-key/two-realm; captured-token Finmap rollback laws | D27 realization/refinement; realm-aware Section 4 theorems deferred |
| D30 | planned/pending | completed/proved | `completed`, `proved` | `MetaAlgebra`, `MetadataPrecedence`, `InterceptionSpec`, `interceptionSpec_support_iff` (`STC/Scoped/Context.lean`) | A I K E | per-key monoid laws checked; presence separated from payload with sound/complete support laws | provider/runtime delivery laws deferred (ADR-10) |
| D31 | planned/pending | completed/proved | `completed`, `proved` | `ScopedContext`, `deriveIntercept` merge/persistence laws, `effectiveMeta`, `ProviderAdapter`, `provideWith` laws (`STC/Scoped/Context.lean`) | A I K E | right precedence explicit via `MetadataPrecedence`; absent-payload inheritance; persistence; provider key-locality | provider uniqueness / runtime service-delivery deferred |
| D27 | deferred/not_applicable | unchanged | — | — | — | — | expository; refinement-only (H04) |
| D74 | deferred/deferred | unchanged | — | — | — | — | refinement phase; only R0 seam planned |

Proposed `target_module` updates: D28 → `STC/Scoped/Resolver.lean`;
D29 → `STC/Scoped/Store.lean`; D30/D31 → `STC/Scoped/Context.lean`.

## Verification record

```text
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped/Model.lean      — exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped/Resolver.lean   — exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped/Store.lean      — exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped/Context.lean    — exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped/Flat.lean       — exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Scoped.lean            — exit 0, no output
$ lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Scoped.lean   — exit 0, no output
$ lake build STC.Scoped.Model STC.Scoped.Resolver STC.Scoped.Store STC.Scoped.Context STC.Scoped.Flat STC.Scoped STC.Examples.Scoped — exit 0 (715 jobs)
$ lake build                                                                          — exit 0 (756 jobs; default target unchanged)
$ python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json     — exit 0, PASS
$ python scripts/scan_lean.py STC                                                     — exit 1 (clean)
$ rg -n '^import .*Control|^import .*Staging|^import .*Support' STC/Scoped.lean STC/Scoped STC/Examples/Scoped.lean — exit 1 (no matches)
$ rg -n 'sorry|admit|axiom|unsafe' STC/Scoped.lean STC/Scoped STC/Examples/Scoped.lean — 2 docstring false positives, classified in P12-scoped-scan-raw.txt
$ git diff --check                                                                     — exit 0
$ git diff --name-only origin/main...HEAD                                              — only P12-owned files
```

Tooling note: the default `lake build` target covers the `STC.lean` import
closure; because `STC/Bootstrap.lean` is outside this lane's ownership, the
`STC.Scoped` family is built through its explicit lake module targets (above)
and the per-file pinned commands. Both were run and pass.

## Integration requests for the post-parallel join

1. Import `STC.Scoped` and `STC.Examples.Scoped` into `STC/Bootstrap.lean`
   (shared file, outside this lane's ownership).
2. Apply the proposed Definition Ledger deltas from the table above.
3. Optional follow-up instance: a `FlatEmbedding` whose `embed` transports an
   arbitrary flat `Finmap` store into `RealmStore M` for a non-identity model
   (needs `Finmap.foldl` step lemmas; the generic contract and laws in
   `STC/Scoped/Flat.lean` already cover any instance, and the identity-model
   instance is fully proved in `STC/Examples/Scoped.lean`).
4. No upstream P5 change was needed: the existing five store laws plus
   `Finmap.ext_lookup` sufficed.
