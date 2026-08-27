# STC Metatheory: P5 Execution Plan

| Field | Value |
|---|---|
| Plan ID | `DH-P5-EXEC-01` |
| Date | 2026-08-28 |
| Repository | `https://github.com/eiKeViN/DeepSeek-STC` |
| Blueprint | `DH-FORMAL-BP-01`, v1.0.2 |
| Planning HEAD | `7502f6e` (`codex/p5-state-registry`, equal to the current P1 branch tip) |
| Required production base | `7502f6e` exactly, observed at the current P1 tip and the other P2-base worktree; P1 must first be merged into `origin/main` |
| Namespace | `STC`; R0 seam under `STC.Adapter.ADR03` |
| Scope | Independently executable portions of `P5-T01` through `P5-T04` |
| Status | Plan complete and resumable; production blocked by `BLOCKER-P5-BASE-01` until P1 PR #3 is merged |

## 1. Objective and acceptance boundary

P5 delivers an abstract state/observation layer, a uniform finite fiber-registry
interface with a nondegenerate `List + Nodup` Toy instance, the minimal
authoritative ADR-02 dependent-`Finmap` façade, and a one-way ADR-03 abstraction
seam. It may use the P1 relation/result foundations, but it must compile without
any P2, P3, or P4 module.

The independently executable result is complete only when it supplies:

1. distinct, explicitly selected observation profiles rather than one implicit
   global state equivalence;
2. kernel-checked registry laws plus finite positive and negative executions;
3. an ADR-02 store façade that remains a dependent coeffect store and is not
   confused with the uniform fiber registry;
4. an R0-only ADR-03 seam that exposes, rather than discharges, concrete
   well-formedness, provenance, and update-preservation obligations;
5. accurate derived ledger evidence, exact validation output, and a fresh
   independent review.

P5 does **not** define an effect, partial operation, iterator, lifecycle step,
alpha action, or runtime adapter. It earns no R1+ evidence and does not verify
Cordis runtime behavior.

## 2. Authority, source anchors, and frozen boundaries

The executing agents must read the repository copies listed below. The
question-relative authority and provenance rules in `AGENTS.md` apply; a
successful Lean build is not permission to change an accepted semantic target.

| Source | P5 anchors consumed |
|---|---|
| `AGENTS.md` | authority model; proof integrity; `STC.Adapter` namespace; frozen/status boundaries; validation loop |
| `docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md` | fixed choices G1, G2, G5 and State carrier; module DAG in section 4; P5 wave in section 5; API sketch in section 6; gates and deferred scope in sections 8-9 |
| `docs/plans/P1-Execution-Plan.md` and `docs/status/P1-handoff-report.md` | P1 ownership decision; frozen `Relation`/`Result` APIs; D33/D37/L38 evidence boundary; exact P1 public declarations |
| `STC/Foundation/Relation.lean` | `RelSpec`, `RespectsOn`, `Respects`, `PointwiseRel`, `CrossRel`, `OptionRel`, `PullbackRel`, `pullbackRelSpec`, and `equality` |
| `STC/Foundation/Result.lean` | result carriers only; P5 must not reinterpret their state, undo, failure, or tag fields |
| ADR-01 JSON | `relation_roles`, `api_contracts`, and coding rules: explicit relation values; named `CoreStateObs`, `LifecycleObs`, `EraseControl`, and name renaming; no automatic refinement between them |
| ADR-02 JSON | `store_architecture`, `store_observation`, global assumptions, and Section-4 provider distinctions: dependent `Finmap`, `DecidableEq K` only at executable boundaries, and exact definedness via `OptionRel` |
| ADR-03 JSON | positive `RawState`, finite registry, `ValidState`, explicit `WellFormed`, provider distinctions, derived active coeffect, update frames, and the observation boundary |
| ADR-03 closure JSON | explicit seven-part `CoreWellFormed`; separate root/catalog boundary predicates; provider provenance; static update gate; preservation and executable-fold proofs still pending |
| ADR-06 JSON | canonical P1 vocabulary; named observation-profile boundaries; concrete state/WF/provider instances excluded from the closure spike; no automatic profile coercions |
| Frozen Formal Reference sections 7-9 | D32 literal recursive carrier defect; D22-D42 coeffect/observation reading; D43-D53 registry/lifecycle concepts and theorem limits |
| Frozen H03 | direct dependencies for D22-D26, D32-D45, D46-D53, D58/T59, D69, `SAT`, and `R.full`; no dependency edge may be edited or inferred |
| Frozen H04 | treatments and repairs for D22-D26, D32-D45, D46-D53, D58/T59, D69, `SAT`, and `R.full`; especially `F-D26-DECIDE`, `F-L35-INVERSE`, and `F-STATE-RECURSION` |

Read-only inputs remain read-only:

```text
docs/blueprint/baseline/
docs/blueprint/architecture-decision/json/
docs/blueprint/architecture-decision/lean-spike/
STC/Foundation/Relation.lean
STC/Foundation/Result.lean
```

Historical ADR spikes may be consulted as provenance, but no production module
may import them. The P0 ruling already makes the repository bytes canonical for
ADR-01, ADR-02, and the ADR-06 spike despite stale Blueprint companion hashes.
Do not edit, normalize, or re-report that known mismatch as a new P5 finding.

## 3. Mandatory base and preflight gate

### BLOCKER-P5-BASE-01

At planning time, `HEAD` is `7502f6e`, while both `main` and `origin/main` are
`02b50d2`. The worktree audit confirmed that `7502f6e` is the exact base used
by the other P2-base worktree. However, P1 PR #3 is still open and draft, and
`7502f6e` is not an ancestor of `origin/main`. The user requires P1 to be
merged before production implementation. Therefore this plan is the only P5
artifact that may be retained before the merge; no Lean, ledger, Bootstrap, or
handoff implementation edit may start while this blocker is open.

Before any production edit:

1. fetch the current remote refs;
2. verify through the repository/PR state that P1 PR #3 is merged, not merely
   closed, open, or marked ready;
3. verify that the complete P1 tip `7502f6e` is an ancestor of `origin/main`;
4. verify that the P5 production `HEAD` is still exactly `7502f6e`, matching
   the confirmed P2 base;
5. if the integration lead changes the P2 base during merge integration, stop
   and obtain one replacement SHA for both P2 and P5 rather than rebasing P5
   independently;
6. record the merge evidence, base SHA, and clean status in the P5 handoff.

Required read-only commands are:

```bash
git fetch origin
git status --short --branch
git log -1 --format='%H %s'
git merge-base --is-ancestor 7502f6e origin/main
git rev-parse HEAD
git rev-parse origin/main
```

If P1 PR #3 is not merged, `7502f6e` is not contained in `origin/main`, or the
P5 `HEAD` differs from the confirmed shared base, keep `BLOCKER-P5-BASE-01`
open and stop production work. Do not approximate “same base” with a
merge-base or a content-equivalent tree. A merge commit on `origin/main` may
contain `7502f6e`; it does not by itself require changing the already confirmed
P2/P5 base.

After the base matches, run and record:

```bash
lake build
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Foundation/Relation.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Foundation/Result.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
git diff --check
```

The planner's cold worktree initially lacked imported `.olean` files, so the
first direct Bootstrap check failed before `lake build`; after the initial
dependency build populated the missing artifacts, a retry of `lake build`
passed with 639 jobs and the direct Bootstrap check exited 0. The ledger
validator passed with 82/82 coverage, and the scan exited 1 with empty output.
The direct Relation and Result checks remain part of the mandatory production
preflight above; they were covered by the planning-time project build but were
not separately rerun. This is planning-time baseline evidence only and must be
rerun on the verified production base.

## 4. Independent scope versus staged scope

| Task | `INDEPENDENT_NOW` work | `DEPENDS_ON_P2_P3_P4` / other deferred work |
|---|---|---|
| `P5-T01` | `StateLike`; generic observation profiles; `CoreStateObs`; lifecycle/control conjunction; distinct `EraseControl`; core-plus-name `NameAwareObs`; pullback and boundary laws; finite separation examples | Effect/result/iterator congruence; lifecycle-step invariance; alpha transport; any claim about execution preserving an observation |
| `P5-T02` | Uniform `RegistryLike`; lookup/insert/erase/domain laws; extensional registry observation; checked fresh-insert and present-erase wrappers; `List + Nodup` Toy instance; finite positive/negative tests | Nested registration, fresh incarnation allocation, lifecycle transitions, provider activation, iterator-driven table completion |
| `P5-T03` | Generic positive `RawState` shell; explicitly factored core/boundary WF predicates; `ValidState`; provider-provenance contract; static checked-update gate; one-way valid-state abstraction contract | Concrete ADR-03 `FiberCell`/active-union instance; concrete WF/provider proofs; transition preservation; runtime simulation/refinement |
| `P5-T04` | Thin `Finmap`-backed dependent coeffect façade and pointwise dependent store observation | ADR-02 binding protocol, specifications/notification, D24 key operations, partial-effect semantics, active-table fold, and mutable/global runtime storage |

The staged column must remain declarations in this plan or explicit obligations
in the handoff, not placeholder Lean declarations. No fake state transition may
be introduced merely to state a preservation result.

## 5. Exact files, import DAG, and ownership

Production files to add:

```text
STC/State/Like.lean
STC/State/Observation.lean
STC/State/RegistryLike.lean
STC/State/Toy.lean
STC/State/CoeffectStore.lean
STC/Adapter/ADR03.lean
STC/Examples/StateRegistry.lean
```

Central integration files to update only after the production modules stabilize:

```text
STC/Bootstrap.lean
docs/status/Definition-Ledger.json
docs/status/P5-scan-raw.txt
docs/status/P5-handoff-report.md
```

The dependency direction is fixed:

```text
STC.Foundation.Relation ────────────────> STC.State.Like
STC.Foundation.Relation + State.Like ──> STC.State.Observation
STC.Foundation.Relation ────────────────> STC.State.RegistryLike ──> STC.State.Toy
Mathlib.Data.Finmap + Foundation.Relation ──> STC.State.CoeffectStore
all State interfaces ───────────────────> STC.Adapter.ADR03
State production modules ───────────────> STC.Examples.StateRegistry
production + examples ─────────────────> STC.Bootstrap ──> STC
```

No P5 module may import `STC.Core.*`, `STC.Alpha.*`, a historical spike, or a
module from an unmerged P2-P4 worktree.

Use one owner per State API file. Workers may edit disjoint production files,
but no worker may concurrently edit `STC/Bootstrap.lean`, the Definition
Ledger, scan output, handoff report, or package configuration. The integration
agent alone owns those central files. The fresh reviewer owns no files.

## 6. API and declaration sketches

These sketches fix semantic shape and ownership. Minor binder order or universe
changes are allowed when required by Lean, but a change to the represented
meaning requires semantic review and a recorded plan amendment.

### 6.1 `STC/State/Like.lean`

`StateLike` contains only the core projection. It is not a validity bundle and
must not hide lifecycle, provider, or transition invariants.

```lean
namespace STC

structure StateLike (S : Type u) (Core : Type v) where
  core : S → Core

structure ObservationProfile (S : Type u) (O : Type v) where
  project : S → O
  obsRel : RelSpec O

def ObservationProfile.stateRel
    (profile : ObservationProfile S O) : RelSpec S :=
  pullbackRelSpec profile.project profile.obsRel

end STC
```

### 6.2 `STC/State/Observation.lean`

The named profiles are explicit relation values. `LifecycleObs` is constructed
as core observation plus separately supplied lifecycle and control profiles.
`NameAwareObs` is core observation plus a separately supplied name view.
`EraseControl` is an independent projection and has no automatic implication
to or from `LifecycleObs`.

```lean
namespace STC

def RelSpec.conj (R T : RelSpec S) : RelSpec S := ...

def CoreStateObs (state : StateLike S Core)
    (coreRel : RelSpec Core) : RelSpec S :=
  pullbackRelSpec state.core coreRel

def LifecycleObs (core : RelSpec S)
    (life : ObservationProfile S Life)
    (control : ObservationProfile S Control) : RelSpec S :=
  RelSpec.conj core (RelSpec.conj life.stateRel control.stateRel)

def EraseControl (erased : ObservationProfile S Erased) : RelSpec S :=
  erased.stateRel

def NameAwareObs (core : RelSpec S)
    (names : ObservationProfile S Names) : RelSpec S :=
  RelSpec.conj core names.stateRel

end STC
```

The concrete lifecycle/control profiles may select `equality` when exact tags
are intended. Later lifted function/iterator relations must be included in an
explicit lifecycle view; P5 does not invent them. Ambient observation also
remains an explicitly stronger profile, not part of `CoreStateObs` by default.

### 6.3 `STC/State/RegistryLike.lean`

`RegistryLike` is a uniform finite fiber registry, not the dependent coeffect
store. Raw `insert` overwrites the binding at one key; `erase` is an absent-key
no-op. Policy-level rejection is expressed by separate checked wrappers.

```lean
namespace STC

structure RegistryLike (K V R : Type*) [DecidableEq K] where
  empty : R
  lookup : R → K → Option V
  insert : R → K → V → R
  erase : R → K → R
  domain : R → List K
  domain_nodup : ∀ r, (domain r).Nodup
  lookup_empty : ∀ k, lookup empty k = none
  lookup_insert_eq : ∀ r k v, lookup (insert r k v) k = some v
  lookup_insert_ne : ∀ r k k' v, k' ≠ k →
    lookup (insert r k v) k' = lookup r k'
  lookup_erase_eq : ∀ r k, lookup (erase r k) k = none
  lookup_erase_ne : ∀ r k k', k' ≠ k →
    lookup (erase r k) k' = lookup r k'
  mem_domain_iff : ∀ r k, k ∈ domain r ↔ (lookup r k).isSome

def RegistryObs (api : RegistryLike K V R) (VRel : RelSpec V)
    (left right : R) : Prop :=
  ∀ k, OptionRel VRel.rel (api.lookup left k) (api.lookup right k)

def registryObsSpec (api : RegistryLike K V R)
    (VRel : RelSpec V) : RelSpec R := ...

def insertFresh? (api : RegistryLike K V R)
    (r : R) (k : K) (v : V) : Option R := ...

def erasePresent? (api : RegistryLike K V R)
    (r : R) (k : K) : Option (V × R) := ...

end STC
```

Carrier equality is deliberately absent from the interface. A `List + Nodup`
registry can contain extensionally equal maps in different list orders;
`RegistryObs` is therefore the correct order-insensitive comparison. Adding an
equality extensionality field would silently impose a canonical ordering not
required by the Blueprint.

### 6.4 `STC/State/Toy.lean`

```lean
namespace STC

structure ToyRegistry (K V : Type*) where
  entries : List (K × V)
  key_nodup : (entries.map Prod.fst).Nodup

def toyRegistryLike [DecidableEq K] :
    RegistryLike K V (ToyRegistry K V) := ...

end STC
```

The Toy implementation uses a list lookup, replacement by remove-then-cons,
and erase by key filtering. Its proof fields discharge every `RegistryLike`
law. The model must have at least three keys and two distinct values; it may
not use an empty key type, singleton-only registry, or proof-irrelevant value
fixture.

### 6.5 `STC/State/CoeffectStore.lean`

This is a thin naming and relation façade over Mathlib `Finmap`; it is not a
second abstract store class and downstream code must not unfold `Finmap`
entries.

```lean
namespace STC.Coeffect

abbrev Store {K : Type u} (Value : K → Type v) := Finmap Value

def lookup [DecidableEq K] (k : K) (store : Store Value) :
    Option (Value k) := Finmap.lookup k store

def keys [DecidableEq K] (store : Store Value) : Finset K := store.keys
def insert [DecidableEq K] (k : K) (value : Value k)
    (store : Store Value) : Store Value := Finmap.insert k value store
def erase [DecidableEq K] (k : K) (store : Store Value) : Store Value :=
  Finmap.erase k store

def StoreObs [DecidableEq K] (KeyObs : ∀ k, RelSpec (Value k))
    (left right : Store Value) : Prop :=
  ∀ k, OptionRel (KeyObs k).rel (lookup k left) (lookup k right)

def storeObsSpec [DecidableEq K] (KeyObs : ∀ k, RelSpec (Value k)) :
    RelSpec (Store Value) := ...

end STC.Coeffect
```

No `Fintype K`, value-wide `DecidableEq`, `Zero`, `Inhabited`, mutable
`rootStore`, global cache, binding transition, or partial-effect definition is
permitted here.

### 6.6 `STC/Adapter/ADR03.lean`

The namespace is singular `STC.Adapter`, following `AGENTS.md`; the Blueprint's
archival `Adapters.Cordis` spelling must not be copied. The seam describes an
ADR-03-shaped source and an abstraction into the P5 model. It contains no
concrete Cordis declaration and no reverse refinement map.

```lean
namespace STC.Adapter.ADR03

structure RawState (Ambient Registry : Type*) where
  ambient : Ambient
  registry : Registry

structure CoreWFSpec (Raw : Type*) where
  parentClosed : Raw → Prop
  parentAcyclic : Raw → Prop
  tableConfined : Raw → Prop
  provisionDisjoint : Raw → Prop
  lifecycleCoherent : Raw → Prop
  committedViewClosed : Raw → Prop
  committedProvidersClosed : Raw → Prop

def CoreWellFormed (spec : CoreWFSpec Raw) (state : Raw) : Prop :=
  spec.parentClosed state ∧ spec.parentAcyclic state ∧
  spec.tableConfined state ∧ spec.provisionDisjoint state ∧
  spec.lifecycleCoherent state ∧ spec.committedViewClosed state ∧
  spec.committedProvidersClosed state

structure BoundaryWFSpec (Raw : Type*) where
  rootSpec : Raw → Prop
  declarationSpec : Raw → Prop

def WellFormed (core : CoreWFSpec Raw) (boundary : BoundaryWFSpec Raw)
    (state : Raw) : Prop :=
  CoreWellFormed core state ∧ boundary.rootSpec state ∧
    boundary.declarationSpec state

abbrev ValidState (core : CoreWFSpec Raw)
    (boundary : BoundaryWFSpec Raw) :=
  { state : Raw // WellFormed core boundary state }

structure ProviderProvenance (Raw Key Provider : Type*)
    (coreWF : Raw → Prop) where
  providesNow : Raw → Provider → Key → Prop
  providerOf : Raw → Key → Option Provider
  provider_sound : ∀ {state key provider},
    providerOf state key = some provider →
      providesNow state provider key
  provider_complete : ∀ {state key provider}, coreWF state →
    providesNow state provider key →
      providerOf state key = some provider
  provider_unique : ∀ {state key left right}, coreWF state →
    providesNow state left key → providesNow state right key → left = right

def checkedUpdate (sameStatic : Raw → Raw → Prop)
    [DecidableRel sameStatic] (before candidate : Raw) : Option Raw :=
  if sameStatic before candidate then some candidate else none

structure StateAbstraction (Raw Abstract Core : Type*)
    (wellFormed : Raw → Prop) where
  abstract : { state : Raw // wellFormed state } → Abstract
  rawCore : Raw → Core
  abstractCore : Abstract → Core
  coreRel : RelSpec Core
  observes : ∀ state,
    coreRel.rel (abstractCore (abstract state)) (rawCore state)

end STC.Adapter.ADR03
```

The provider proof fields and `StateAbstraction.observes` are R0 admission
obligations. Merely constructing the record type proves none of them for the
ADR-03 carrier. The named component predicates remain available individually;
no later theorem may replace a needed acyclicity, confinement, disjointness, or
provider hypothesis with an opaque `WellFormed` premise.

The checked gate proves only that a successful candidate satisfies
`sameStatic`. It does not prove `CoreWellFormed` preservation. A checked
operation that claims WF preservation must additionally prove every affected
predicate for its actual semantics.

## 7. Observation profiles and registry-law contract

### Observation inventory

| Profile | Observes | Intentionally does not imply |
|---|---|---|
| `CoreStateObs` | only the explicitly supplied core projection; for ADR-03 this will later be active coeffect/`StoreObs` | ambient equality, registry identity, lifecycle/control equality, name equality |
| `LifecycleObs` | `CoreStateObs` plus explicit lifecycle and control profiles | `EraseControl`, alpha equivalence, raw execution equality |
| `EraseControl` | an explicit control-erasing projection chosen for recovery statements | `LifecycleObs`; ADR-01 states no refinement in either direction |
| `NameAwareObs` | core observation plus an explicit name-bearing view | name renaming as default equality; P6 must supply actions/transport |
| `Coeffect.StoreObs` | same dependent key definedness and per-key related values | fiber identity, provider identity, registry order, runtime object identity |
| `RegistryObs` | same uniform key definedness and related fiber-cell values | list order or representation equality |

The Toy examples must witness at least two observer boundaries: one pair related
by `LifecycleObs` but not `NameAwareObs`, and one pair related by
`EraseControl` but not `LifecycleObs`. This prevents accidental collapse to a
single behavior-erasing relation.

### `RegistryLike` law strength

The structure fields are interface assumptions until an instance discharges
them. The Toy instance must prove all of them.

| Law family | Required meaning |
|---|---|
| finite uniqueness | every reported domain is `Nodup` |
| lookup/domain | domain membership iff lookup is defined |
| empty | every lookup in `empty` is `none` |
| insert same key | lookup of the inserted key is the inserted value |
| insert frame | every distinct-key lookup is unchanged |
| erase same key | erased-key lookup is `none` |
| erase frame | every distinct-key lookup is unchanged |
| extensional observation | registry comparison is pointwise tag-strict `OptionRel`, not raw list equality |
| checked fresh insert | duplicate keys produce `none`; absence produces the raw insert |
| checked present erase | missing keys produce `none`; success returns the captured value and erased registry |
| local recovery | erase after a fresh insert and reinsert after captured erase recover the original registry under `RegistryObs (equality V)` |

These are data-structure laws. They do not establish fresh incarnation
allocation, lifecycle legality, provider selection, transition preservation, or
runtime behavior.

## 8. Exhaustive theorem classification

Every theorem planned by this document appears below. Helper theorems added
during implementation must first be added to this table with one of the two
required classifications. Structure proof fields and `RelSpec` constructors
are assumptions/definitions, not standalone theorem claims; their concrete Toy
proofs still contribute K evidence.

### 8.1 Theorems to implement in P5

| Theorem | File | Classification | Intended evidence |
|---|---|---|---|
| `ObservationProfile.project_respects` | `State/Like.lean` | `INDEPENDENT_NOW` | K: projection respects its exact pullback relation |
| `pullback_comp` | `State/Observation.lean` | `INDEPENDENT_NOW` | K: nested observation pullback agrees with composed projection |
| `lifecycleObs_iff` | `State/Observation.lean` | `INDEPENDENT_NOW` | K: exposes all three conjuncts, preventing hidden observation |
| `lifecycleObs_implies_core` | `State/Observation.lean` | `INDEPENDENT_NOW` | K |
| `lifecycleObs_implies_lifecycle` | `State/Observation.lean` | `INDEPENDENT_NOW` | K |
| `lifecycleObs_implies_control` | `State/Observation.lean` | `INDEPENDENT_NOW` | K |
| `nameAwareObs_iff` | `State/Observation.lean` | `INDEPENDENT_NOW` | K: exposes core and name components |
| `nameAwareObs_implies_core` | `State/Observation.lean` | `INDEPENDENT_NOW` | K |
| `nameAwareObs_implies_names` | `State/Observation.lean` | `INDEPENDENT_NOW` | K |
| `registryObs_lookup` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: related registries have tag-strict related lookups |
| `registryObs_same_domain` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: observation preserves membership/definedness |
| `registryObs_insert` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: related registries and values remain related after same-key insert |
| `registryObs_erase` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: same-key erase preserves registry observation |
| `domain_insert_iff` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: membership is inserted key or old membership |
| `domain_erase_iff` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: membership is distinct key and old membership |
| `insertFresh?_eq_none_iff` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: duplicate rejection iff key was present |
| `insertFresh?_success` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: absence yields raw insert and inserted lookup |
| `erasePresent?_eq_none_iff` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: failure iff key was absent |
| `erasePresent?_success` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: success captures old value and removes key |
| `erase_insert_of_absent_obs` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: fresh insert followed by erase recovers observationally |
| `insert_erase_of_lookup_obs` | `State/RegistryLike.lean` | `INDEPENDENT_NOW` | K: captured erase followed by insert recovers observationally |
| `coeffect_lookup_empty` | `State/CoeffectStore.lean` | `INDEPENDENT_NOW` | K: façade theorem over authoritative `Finmap` |
| `coeffect_mem_keys_iff` | `State/CoeffectStore.lean` | `INDEPENDENT_NOW` | K: finite domain agrees with defined lookup |
| `coeffect_lookup_insert` | `State/CoeffectStore.lean` | `INDEPENDENT_NOW` | K |
| `coeffect_lookup_insert_ne` | `State/CoeffectStore.lean` | `INDEPENDENT_NOW` | K |
| `coeffect_lookup_erase` | `State/CoeffectStore.lean` | `INDEPENDENT_NOW` | K |
| `coeffect_lookup_erase_ne` | `State/CoeffectStore.lean` | `INDEPENDENT_NOW` | K |
| `coeffectStoreObs_same_keys` | `State/CoeffectStore.lean` | `INDEPENDENT_NOW` | K: `OptionRel` definedness gives equal key domains |
| `checkedUpdate_eq_some_iff` | `Adapter/ADR03.lean` | `INDEPENDENT_NOW` | K for the static gate only; no WF claim |
| `checkedUpdate_eq_none_iff` | `Adapter/ADR03.lean` | `INDEPENDENT_NOW` | K for rejected candidates only |
| `toy_lifecycle_not_nameAware` | `Examples/StateRegistry.lean` | `INDEPENDENT_NOW` | K/E: nontrivial profile-separation witness |
| `toy_eraseControl_not_lifecycle` | `Examples/StateRegistry.lean` | `INDEPENDENT_NOW` | K/E: nontrivial profile-separation witness |
| `stateRegistryReport_expected` | `Examples/StateRegistry.lean` | `INDEPENDENT_NOW` | K/E: exact finite report checked by `decide` |

No theorem asserting a relationship between `EraseControl` and `LifecycleObs`
is planned; the accepted architecture explicitly forbids assuming one.

### 8.2 Theorems that must remain unstated in production P5

These names reserve downstream obligations only. They are not placeholder Lean
declarations and must not appear in `STC` during this wave.

| Reserved theorem obligation | Earliest owner | Classification | Missing dependency/hypothesis |
|---|---|---|---|
| `effect_preserves_validState` | P2/P5 integration | `DEPENDS_ON_P2_P3_P4` | actual shallow Effect semantics plus explicit preservation hypotheses |
| `partialOp_preserves_validState` | P3/P5 integration | `DEPENDS_ON_P2_P3_P4` | partial run, definedness, successor, and checked-failure semantics |
| `iterator_preserves_validState` | P4/P5 integration | `DEPENDS_ON_P2_P3_P4` | ranked stages, continuation execution, and per-stage preservation |
| `lifecycle_step_respects_lifecycleObs` | later control integration | `DEPENDS_ON_P2_P3_P4` | authoritative labelled lifecycle relation and result/iterator relations |
| `provider_transition_preserves_provenance` | P3/control integration | `DEPENDS_ON_P2_P3_P4` | actual provider-changing transition semantics and frame laws |

Alpha-renaming/transport theorems belong to P6, not to the P5 theorem plan, so
they are compatibility consumers rather than misclassified P5 obligations.
Concrete provider-choice adequacy, active-union completeness, and checked raw
update WF preservation are likewise exposed as R0 obligations but are not
planned theorem declarations in this wave: their concrete ADR-03 instance has
not been scheduled, and falsely labelling these static adapter obligations as
P2/P3/P4 dependencies would violate the classification discipline.

## 9. Executable-test minimum set

`STC/Examples/StateRegistry.lean` must define one finite report evaluated with
`#eval` and asserted with `stateRegistryReport_expected`. At minimum it records:

```text
emptyLookup = none
insertLookup = some value
distinctLookupFramed = true
rawOverwriteUpdated = true
rawOverwriteDomainNodup = true
duplicateFreshInsertRejected = true
missingLookup = none
missingEraseRejected = true
presentEraseCapturedValue = true
presentEraseRemovedKey = true
freshInsertEraseRecovered = true
capturedEraseInsertRecovered = true
lifecycleRelatedButNameAwareRejected = true
eraseControlRelatedButLifecycleRejected = true
dependentCoeffectNatLookup = expected Nat value
dependentCoeffectBoolLookup = expected Bool value
```

Use an inductive coeffect key with at least two constructors and a genuinely
dependent family, for example one key carrying `Nat` and another carrying
`Bool`. This is the executable witness that the coeffect façade is not the
uniform Toy registry. Negative fixtures must execute to `false`/`none`; merely
stating a Prop is not E evidence. Tests supplement but never replace generic K
proofs.

## 10. Task execution, gates, and collaboration

### P5-T01 — State and observations

Owner files: `STC/State/Like.lean`, then `STC/State/Observation.lean`.

1. Implement the small `StateLike` and generic `ObservationProfile`.
2. Implement named relations and only the theorems listed in section 8.1.
3. Audit that profile arguments are explicit and no global `Setoid` is used.
4. Run the two per-file Lean checks before handing the API to other workers.

Gate: A/I/K for generic observation boundaries; no E until the example file.

### P5-T02 — Registry and Toy model

Owner files: `STC/State/RegistryLike.lean`, then `STC/State/Toy.lean`.

1. Freeze the raw registry contract before implementing the Toy instance.
2. Prove all lookup/domain/frame and checked-wrapper theorems.
3. Instantiate the contract with `List + Nodup` without quotienting execution.
4. Use `RegistryObs`, not list equality, for order-insensitive recovery.

Gate: I/K for the generic API and every Toy law field. Do not start D47 nested
registration or fresh-name semantics.

### P5-T04 — ADR-02 dependent coeffect façade

Owner file: `STC/State/CoeffectStore.lean`.

1. Audit the pinned Mathlib `Finmap` signatures before porting wrappers.
2. Expose only lookup, keys, insert, erase, `StoreObs`, and listed laws.
3. Keep dependent values and avoid requiring equality for all values.
4. Document that this store is held by fibers and later aggregated; it is not
   the registry and not a mutable root/global cache.

Gate: A/I/K. Full ADR-02 specification/notification/partiality remains outside
P5.

### P5-T03 — ADR-03 R0 seam

Owner file: `STC/Adapter/ADR03.lean`.

1. Define the positive generic raw shell and explicitly named WF components.
2. Keep root/catalog predicates separate from `CoreWellFormed`.
3. Define provider provenance as a contract with visible soundness,
   completeness, and uniqueness obligations.
4. Implement only the static checked-update gate and its two exact theorems.
5. Define a one-way valid-state abstraction contract using an explicit core
   relation.

Gate: A/I/R0 plus K only for the generic static-gate equations. Do not award K
for provider/WF fields until a concrete instance proves them.

### Examples and central integration

Owner file: `STC/Examples/StateRegistry.lean`, followed serially by the central
files.

1. Add the finite report and negative observer/registry fixtures.
2. Run every new-file check and `lake build`.
3. Update `STC/Bootstrap.lean` imports only after production modules pass.
4. Edit affected ledger rows in place; never run
   `scripts/gen_definition_ledger.py`.
5. Save the exact final scan output to `docs/status/P5-scan-raw.txt`.
6. Draft `docs/status/P5-handoff-report.md` from actual results.

Suggested focused commits are:

```text
p5: add explicit state observation profiles
p5: add registry interface and finite toy model
p5: add dependent coeffect facade and ADR03 seam
p5: integrate examples bootstrap and evidence
p5: address independent review findings
```

Sol owns semantic planning/escalation; Luna is the default implementation role
for routine definitions, instances, proofs, tests, docs, and build repair. A
fresh Sol context performs the independent review. If exact model routing is
unavailable, record that limitation while preserving disjoint ownership and a
fresh reviewer context.

## 11. Definition Ledger rows and expected evidence

Only derived fields may change. Preserve every `depends_on`, H03/H04 field,
treatment, paper anchor, and frozen readiness value. Update the ledger's plan
metadata to `DH-P5-EXEC-01` and edit rows in place after actual evidence exists.

| Row | Expected post-P5 delivery/evidence if all gates pass | P5 interpretation |
|---|---|---|
| D22 | `completed` / `proved` | authoritative dependent `Finmap` façade and checked lookup/domain/update laws |
| D32 | `in_progress` / `seam_only` | abstract `StateLike` plus positive `RawState`/`ValidState` R0 seam; no full ADR-03 realization/refinement theorem |
| D33 | `completed` / `proved` | dependent `StoreObs`, explicit state pullback, and distinct observation profiles with checked boundary laws |
| D44 | `in_progress` / `aligned` | uniform registry shell/Toy instance only; no full FiberCell behavior/lifecycle payload |
| D45 | `in_progress` / `seam_only` | finite registry laws and provider-provenance seam; active union/provider instance remains |
| D53 | `planned` / `aligned` | profile names/boundaries aligned only; traces, episodes, steps, and alpha remain later |
| D58 | `in_progress` / `seam_only` | explicit WF component interface and boundary split; no concrete preservation proof |

Rows D23-D26, D34-L35, D39-T42, D43, D46-D50, T59, D69, `SAT`, and
`R.full` must not be promoted merely because their carrier dependencies now
exist. In particular:

- D46 target/quiescence remains staged by lifecycle/staging semantics;
- D47 remains staged by control and lifetime-safe fresh allocation;
- T59 remains deferred until an authoritative step relation exists;
- D25/D26/`SAT` are not implemented by a small store façade;
- D34/L35 and D39-T42 remain P3/coeffect-operation work.

If implementation evidence is weaker than the expectation above, record the
weaker truthful vocabulary value; never promote a row from compilation alone.

## 12. Validation and evidence gates

After each changed Lean file, run:

```bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Like.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Observation.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/RegistryLike.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/Toy.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/State/CoeffectStore.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Adapter/ADR03.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/StateRegistry.lean
```

At each integration checkpoint and after review fixes, run:

```bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
git diff --check
git status --short --branch
```

Interpret the scan contract exactly: exit 1 is clean, exit 0 means matches that
must be inspected/classified, and exit 2 is an error. Record stdout, stderr,
and exit codes; do not transform an expected exit 1 into a false command
failure in the handoff.

| Gate | Required P5 evidence | Does not establish |
|---|---|---|
| G-A | source mapping, scope review, observer/store distinction, non-vacuity review | theorem truth |
| G-I | every new module, Bootstrap, and package elaborate with the pinned options/toolchain | laws or semantic alignment |
| G-K | all section 8.1 propositions and all Toy instance law fields have placeholder-free checked proof terms | concrete ADR-03 WF/provider preservation |
| G-E | exact finite report, positive/negative registry cases, dependent store values, and profile separation execute | generic theorem validity alone |
| G-R0 | ADR-03 carrier/validity/provenance/update/abstraction contract elaborates | any concrete state or runtime refinement |
| G-H | validator and provenance checks pass without frozen edits | correctness of paper claims or ADRs |

Production remains free of `sorry`, `admit`, project-defined unchecked
`axiom`, and `unsafe`. No impossible invariant, empty relation, degenerate
registry, behavior-erasing observation, or fabricated transition may satisfy a
gate.

## 13. Stop conditions and escalation protocol

Stop affected work and escalate to Sol when any of the following occurs:

1. `BLOCKER-P5-BASE-01` remains open.
2. P5 appears to require a change to frozen `Relation.lean` or `Result.lean`.
3. A proposed `StateLike` starts carrying hidden WF, provider, effect, iterator,
   or control obligations.
4. `LifecycleObs`, `EraseControl`, or `NameAwareObs` is collapsed into another
   profile or given an unapproved automatic refinement/coercion.
5. Registry equality requires canonical list ordering or proof irrelevance not
   present in the accepted design.
6. The uniform registry and dependent coeffect store begin sharing one mutable
   carrier or update path.
7. A provider/WF theorem needs an unmerged operation, effect, iterator, or
   lifecycle semantics.
8. A concrete ADR-03 instance would require resolving BD-CONTROL, BD-STAGING,
   BD-SUPPORT, BD-SCOPED, or P6 alpha semantics.
9. A theorem is false, vacuous, or needs a hypothesis not authorized by an ADR.
10. Any final build, validator, scan, or diff gate fails.

If a frozen P1 API is the cause, create a report named `BLOCKER-P5-*` containing
the exact declaration/signature, the missing capability, the minimal proposed
change, dependent P5 tasks, and a counterexample or compiler goal when
available. Do not edit the frozen file and stop only the dependent work.

Every semantic escalation returns exactly one of: approved proof strategy,
corrected theorem/interface, explicit missing hypothesis, staged dependency,
counterexample, or blocker. Compilation convenience alone is not an
architectural decision.

## 14. P6/P7/P8 compatibility

- P6 can act on the explicit name-bearing view without changing raw execution
  equality. `NameAwareObs` retains names; `CoreStateObs` and `EraseControl` do
  not make alpha equivalence implicit.
- P6 may define permutation actions for registry keys/cells and prove transport
  against `RegistryObs`; the P5 list representation is not exposed as the
  semantic equality.
- P7 can instantiate `StateLike` for the two-counter state, add distinct
  counter/effect behavior, reuse the Toy registry checks, and select equality or
  observational profiles explicitly.
- P2-P4 remain upstream-independent: they need not import P5 to compile. Later
  integration may import the P5 interfaces and discharge the reserved
  preservation obligations.
- P8 may connect a concrete implementation only through a new R1+ refinement;
  the P5 `StateAbstraction` is one-way R0 evidence and must not be relabelled.

No P5 declaration may bake alpha equivalence into equality, discard names from
all views, identify provider identity with mere key presence, or equate a
`Finmap` coeffect store with the registry carrier.

## 15. Independent review and handoff

After implementation and validation, invoke a fresh Sol reviewer. The reviewer
must inspect the actual diff and the sources in section 2, not the worker
summary. Review at minimum:

1. smallness of `StateLike` and visibility of all invariants;
2. separation and non-vacuity of all observation profiles;
3. use of P1 pullback/`OptionRel` vocabulary;
4. RegistryLike law sufficiency and absence of unjustified carrier equality;
5. correctness of the `List + Nodup` implementation and negative cases;
6. dependent ADR-02 store versus uniform ADR-03 fiber registry;
7. `RawState`/`ValidState`/WF boundary fidelity;
8. provider provenance and checked-update claim strength;
9. independence from P2-P4 and compatibility with P6;
10. absence of fake preservation/refinement claims;
11. theorem non-vacuity, executable output, ledger accuracy, and exact gates.

The verdict is `PASS`, `PASS_WITH_FIXES`, or `BLOCK`. Structured fixes go only
to the owning implementation worker; rerun the complete validation and obtain
a fresh re-review after fixes.

The final `docs/status/P5-handoff-report.md` must have the top-level sections:

```text
COMPLETED_NOW
STAGED_FOR_P2_P3_P4
DEFERRED_TO_P6_OR_LATER
BLOCKED
```

It must record the base and final SHAs, branch, changed files, public
definitions, exhaustive theorem inventory with classifications, observation
inventory, RegistryLike laws, exact Toy output, negative fixtures, ADR-02/03
boundary, R0 seams and admission obligations, evidence A/I/K/E/R0/R1+, ledger
changes, exact validation output, unresolved dependencies, reviewer verdict,
and confirmation that frozen inputs and P1 APIs were untouched.

After a `PASS`, create focused commits, push `codex/p5-state-registry`, and open
or update a review-ready PR to `main`. Stop before merge; never automatically
merge the PR.

## 16. Resolved planning ambiguities

1. **Blueprint path spelling.** Use `STC/Adapter/ADR03.lean` and namespace
   `STC.Adapter.ADR03`; `AGENTS.md` supersedes the Blueprint's archival
   `Adapters.Cordis` example for implementation workflow.
2. **Two finite maps.** `RegistryLike K V R` is a uniform fiber registry and
   its Toy carrier is `List + Nodup`. `STC.Coeffect.Store Value` is the
   authoritative dependent ADR-02 `Finmap`; neither replaces the other.
3. **Toy extensionality.** Because list order is not canonical, the plan uses
   `RegistryObs` rather than raw carrier equality.
4. **Checked update.** P5 checks only an explicit static-field relation. Full WF
   preservation is staged and cannot be inferred from that gate.
5. **Provider evidence.** Soundness/completeness/uniqueness are visible R0
   record obligations. They earn K only when a concrete instance proves them.
6. **Frozen readiness.** Accepted ADRs affect effective interpretation, but P5
   does not rewrite H03 edges or H04 blocker/readiness fields; only derived
   ledger delivery/evidence fields change.

The exact shared post-P1/P2 base is resolved as `7502f6e`. The only open
planning blocker is the required merge of P1 PR #3, recorded as
`BLOCKER-P5-BASE-01`.
