# STC Metatheory: P5 Execution Plan

| Field | Value |
|---|---|
| Plan ID | `DH-P5-EXEC-01` |
| Repository | `https://github.com/eiKeViN/DeepSeek-STC` |
| Prepared | 2026-08-28 |
| Baseline | `origin/main` at `9969ec5` (P0, P1, and P2 merged) |
| Blueprint | `DH-FORMAL-BP-01`, v1.0.2 |
| Scope | abstract state, observation, registry, and ADR-03 adapter interfaces |
| Ownership | One agent, parallel with the P3→P4 workstream |
| Namespace | `STC` |
| Adapter boundary | `STC.Adapter` remains reserved; this wave exposes state-side R0 seams only |
| Status | Ready after preflight |

The P5 branch may be merged before or after the P3→P4 branch once its own gate
passes. P6 must wait for both handoffs; no P5 task is allowed to depend on an
unreviewed iterator implementation.

## 1. Mission and boundary

This wave supplies the state-side interfaces needed by later lifecycle and
alpha-transport work: an abstract `StateLike`/observation layer, a finite
`RegistryLike` with a Toy implementation, and a one-way seam toward the
ADR-03 positive finite state architecture.

P5 is intentionally independent of the P3→P4 partial/iterator workstream. It
must not implement lifecycle control, ranked execution, concrete Cordis code,
or the full ADR-02 coeffect calculus. In particular:

- `RegistryLike` models the fiber registry, not the authoritative dependent
  coeffect store;
- `RawState`, `ValidState`, and `WellFormed` are represented by an
  explicit adapter contract before any concrete provider/WF proof is attempted;
- a compiling interface earns `I` or `R0`, not automatic state semantics or
  runtime refinement.

## 2. Baseline and preflight

Start a fresh branch from the current remote main:

```bash
git fetch origin --prune
git switch -c <p5-branch> origin/main
git status --short --branch
git log -1 --oneline
```

At planning time `origin/main = 9969ec5`. It contains the merged P1
relation/result foundation and P2 shallow Effect kernel. Treat those public APIs
as stable dependencies; do not rewrite them to make P5 convenient.

Read without modifying:

```text
AGENTS.md
README.md
lean-toolchain
lakefile.toml
lake-manifest.json
STC.lean
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
docs/blueprint/baseline/DeepSeek-Harness-01-Formal-Reference.md
docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json
docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.json
docs/blueprint/architecture-decision/json/*.json
docs/status/P0-baseline.json
docs/status/P1-handoff-report.md
docs/status/P2-handoff-report.md
docs/status/Definition-Ledger.json
STC/Foundation/Relation.lean
STC/Foundation/Result.lean
STC/Core/Effect.lean
STC/Bootstrap.lean
```

The Project Guide and Research Ledger are project-history documents and are not
formalization dependencies. Historical ADR spikes are read-only compiler
mirrors; never import or copy them into production.

Run the baseline gate before production edits:

```bash
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
```

The scanner contract is: exit `1` = clean, exit `0` = lexical match, exit `2` =
error. A missing compiler is `blocked`. Verify H03/H04 and the accepted ADR
hashes against `docs/status/P0-baseline.json`.

## 3. Dependency and parallel-work contract

P5's internal order is:

```text
P5-T01 StateLike/observation
  → P5-T02 RegistryLike + Toy
  → P5-T03 ADR-03 adapter seam
  → P5-T04 store/registry boundary
```

T03 and T04 may be developed in parallel after T02, but the public state and
registry interfaces must be frozen first. P3/P4 may proceed concurrently in
different files. Neither workstream may edit these integration-owned paths:

```text
STC.lean
STC/Bootstrap.lean
docs/status/Definition-Ledger.json
docs/status/P5-scan-raw.txt
docs/status/P5-handoff-report.md
```

The P5 agent owns only `STC/State/**` and, if a separate fixture is useful,
`STC/Examples/State.lean`; it must not touch the P3/P4 example paths. The user
or integration owner performs the cumulative imports, ledger updates, scan
record, and merge review after both workstreams report.

## 4. P5-T01 — StateLike and observation profiles

Primary files: `STC/State/Like.lean` and, if useful, a separate
`STC/State/Observation.lean`.

Define a small abstract state projection and explicit observation profiles.
`ObservationProfile` should extend or compose `StateLike`; do not duplicate a
second unrelated `project` field without documenting the coherence equation.
A suitable starting shape is:

```lean
structure StateLike (S : Type u) (O : Type v) where
  project : S → O

structure ObservationProfile (S : Type u) (O : Type v) extends StateLike S O where
  stateRel : RelSpec S
  obsRel : RelSpec O
  project_respects :
    RespectsOn stateRel.rel obsRel.rel project

def inducedRel (p : ObservationProfile S O) : RelSpec S :=
  pullbackRelSpec p.project p.obsRel
```

Reuse P1's `RelSpec`, `RespectsOn`, `PullbackRel`, `PiRel`, and
`optionRel_isSome_iff` rather than creating a second relation vocabulary or
duplicating definedness case splits. Keep these observation boundaries as
distinct named profiles:

- core state/coeffect observation;
- lifecycle-state observation;
- control-erasing observation;
- name-aware observation for the later alpha boundary.

Do not identify them merely because they share an underlying carrier. Do not
put the freshness ledger into the default core observation; ADR-04 places that
at the orchestration/trace boundary.

`PullbackRel project obsRel` is the explicitly induced relation. A supplied
`stateRel` is accepted only with an explicit refinement direction: the current
`project_respects` field establishes `stateRel ⊆ inducedRel`. If the two
relations are claimed to coincide, provide both directions (or an explicit
equality/refinement field) rather than relying on the shared carrier or
projection. Required generic evidence:

- pullback of an observation relation is an explicit relation value;
- the profile's projection respects its supplied relation;
- an equality specialization and one nontrivial finite observation example.

Concrete coeffect keys, provider selection, and lifecycle semantics remain
deferred. Do not encode them as hidden fields in an oversized WF predicate.

## 5. P5-T02 — RegistryLike and Toy registry

Primary files: `STC/State/RegistryLike.lean` and
`STC/State/Toy.lean`.

Define the fiber-registry interface with explicit lookup/update/domain
operations and laws. A suitable abstract shape is:

```lean
structure RegistryLike (K V R : Type u) [DecidableEq K] where
  empty : R
  lookup : R → K → Option V
  insert : R → K → V → R
  erase : R → K → R
  dom : R → List K
  dom_nodup : ∀ r, (dom r).Nodup
  lookup_empty : ∀ k, lookup empty k = none
  lookup_insert_eq : ∀ r k v, lookup (insert r k v) k = some v
```

The exact fields may grow when a proof needs them, but avoid assuming
`Fintype K` or decidable equality on dependent values unless a concrete Toy
instance requires it. State the laws needed for lookup after insert/erase,
domain membership, and preservation of `Nodup`.

Instantiate a finite Toy registry using `List + Nodup`. Include positive and
negative executable checks for:

- insertion and lookup;
- erasure and absence;
- duplicate-key/domain behavior;
- a deliberately law-breaking operation rejected by a Boolean/proposition
  negative check (do not try to construct an invalid `RegistryLike` instance).

This Toy registry is an executable witness, not the final ADR-03 `Finmap`
implementation and not a replacement for ADR-02's dependent store.

## 6. P5-T03 — ADR-03 state adapter seam

Primary file: `STC/State/FinmapAdapter.lean`. This is a state-side contract
module, not the reserved `STC/Adapter.lean` runtime/refinement namespace;
leave the latter untouched in P5.

Expose a one-way, type-parametric interface connecting an abstract state
carrier to the ADR-03 concepts:

```text
abstract state S
  → raw-state observation / projection
  → optional ValidState/WF witness
  → checked update preserving declared static fields
```

The interface may name or parameterize:

- `RawState`-like data;
- `ValidState` as a subtype or proof-indexed wrapper;
- `WellFormed`;
- provider provenance and committed-view lookup;
- `checkedModify` or an equivalent checked update operation.

It must not store `State → State` closures in registry cells, introduce an
implicit mutable `rootStore`, or import the ADR-03 spike. Keep static-field
projection, checked-update preconditions, and provider/lifecycle visibility
explicit.

The first deliverable is an interface and at most generic preservation lemmas
whose hypotheses are visible. Concrete `RawState` field proofs, provider
adequacy, lifecycle visibility, and `WellFormed` preservation are later
obligations. Classify this task as `I/R0` unless a genuine theorem is proved.

## 7. P5-T04 — store/registry boundary

Primary file: `STC/State/Observation.lean` (required; it may contain the T01
profiles or a narrowly named façade, but it must not remain an optional path).

Document and, where useful, type-check the distinction:

```text
fiber registry: RegistryLike / Toy / later ADR-03 `Finmap` registry
coeffect store: ADR-02 dependent Finmap (authoritative)
coeffect view: derived from currently providing fibers
```

Expose only a compatible façade or projection interface. Do not create a
second authoritative mutable global store, and do not silently equate a
registry domain with a coeffect key domain. Provider uniqueness, active-store
fold order independence, and lifecycle timing remain explicit deferred
contracts.

## 8. Paper rows and evidence boundary

P5 supplies infrastructure for D32/D33 and D44–D47, but completion remains
granular:

| Rows | P5 may deliver | Still deferred |
|---|---|---|
| D32 | positive abstract state/adapter shell | full unified calculus and lifecycle semantics |
| D33 | concrete observation profile/pullback bridge | complete coeffect/state equivalence theorem |
| D44–D47 | finite registry data and lookup/update contracts | control rules, provider adequacy, nested registration |
| D22–D31 | store/registry boundary notes and façade hooks | full ADR-02 coeffect operations and scoped realms |

Do not edit H03 dependency lists or H04 readiness fields. Update only derived
ledger evidence after integration, and do not mark BD-COEFFECT, BD-CONTROL,
BD-STAGING, BD-SUPPORT, or BD-SCOPED resolved by compiling an interface.

## 9. Validation and handoff

Focused checks for the P5 branch are:

```bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Like.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/RegistryLike.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Toy.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/FinmapAdapter.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Observation.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
```

The final scan must exit `1`; preserve its raw output at integration. Every
focused check and `lake build` must finish with zero errors and zero warnings.
Record evidence separately:

| Evidence | P5 interpretation |
|---|---|
| `A` | paper/ADR mapping and explicit observation boundary |
| `I` | state/registry modules elaborate and imports are acyclic |
| `K` | checked generic registry/profile laws only |
| `E` | finite Toy registry/observation evaluations |
| `R0` | adapter interface or checked-update seam |
| `R1+` | not earned by P5 |

The handoff must include task ownership, base/final commits, changed paths,
public declarations, exact command outcomes, finite test outputs, rows whose
status changed, deferred WF/provider assumptions, and confirmation that P3/P4
files, frozen inputs, and historical spikes were untouched.

The AGENTS.md ledger rule still applies. During parallel development the
central `Definition-Ledger.json` and scan/report paths are integration-locked;
the P5 agent supplies an exact derived-row patch and raw scan output, while the
integration owner applies them after review. This is an ownership exception,
not permission to omit or rewrite evidence.

Stop and request review if a proposal duplicates the P1/P2 carriers, imports a
historical spike, conflates registry and coeffect store, hides provider/WF
premises, or introduces concrete Cordis declarations. Suggested commits:

```text
p5: add abstract state and observation profiles
p5: add RegistryLike and Toy registry
p5: add ADR-03 adapter boundary
p5: record store-registry separation and finite evidence
```
