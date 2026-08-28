# STC Metatheory: P6 Execution Plan — Alpha Transport

| Field | Value |
|---|---|
| Plan ID | `DH-P6-EXEC-01` |
| Repository | `https://github.com/eiKeViN/DeepSeek-STC` |
| Prepared | 2026-08-28 |
| Baseline | `origin/main` at `a72e3d7` (P0–P5 and the P3/P4 merge) |
| Blueprint | `DH-FORMAL-BP-01`, v1.0.2 |
| Scope | name-neutral alpha transport, plus explicit trace/freshness boundary interfaces |
| Ownership | one agent, sequentially; the Core API is frozen before transport work |
| Dependencies | merged P3/P4 and P5 production APIs; accepted ADR-04 and ADR-06 |
| Namespace | `STC`; alpha modules under `STC/Alpha/` |
| Adapter boundary | `STC.Adapter` remains reserved for the future runtime/refinement seam |
| Status | ready after preflight |

P6 is the next production wave after P3, P4, and P5. It consumes the accepted
ADR-04 incarnation/freshness architecture and ADR-06 equivariance contracts; it
does not reopen either decision. The implementation is intentionally split
between a generic action/transport layer and an orchestration-side freshness
boundary. A name-neutral theorem profile is useful now, while name-bearing
control and runtime semantics remain later work.

## 1. Mission and non-goals

P6 turns the alpha-renaming part of the accepted architecture into production
interfaces and checked theorems over the current P2/P4 carriers:

```text
Equiv.Perm N
    ├── state action and conjugated undo
    ├── EffectResult / Failure / ExecResult / StageResult
    ├── RankedIterator and well-founded execution
    └── explicit trace/freshness metadata boundary
```

The first transport profile assumes that the state carrier may contain names,
but that the error carrier and continuation code are name-neutral. In that
profile `E` and `Q` are intentionally left unchanged. This is a real,
restricted theorem, not a claim that arbitrary payloads are opaque.

P6 must not:

- alter the P1–P5 public carriers or theorem statements;
- put the ever-issued ledger into P5's default `CoreStateObs`;
- identify alpha-renaming with any `RelSpec` observation;
- introduce a second iterator, failure carrier, registry, or coeffect store;
- define lifecycle/control rules, asynchronous landing, support recursion,
  confluence, scoped realms, or concrete Cordis behavior;
- claim equivariance for name-bearing `Q`, `Xi`/errors, ambient values,
  accumulators, target hashes, interpreter closures, or control labels without
  explicit actions and interpreter laws;
- claim runtime atom/generation correspondence or R1+ refinement.

The accepted ADR-04 rule remains in force: `IncarnationId` is an opaque
lifetime-level identity, while current-registry freshness and the monotone
ever-issued ledger are distinct predicates. P6 may parameterize this layer by
an abstract `N`; it must not silently make `N` a concrete runtime atom type.

## 2. Authority, source boundaries, and preflight

Repository bytes at the current remote `main` are the implementation baseline.
The paper remains authoritative for literal source claims; the Formal Reference
and frozen H03/H04 files are provenance records; accepted ADR-01–06 are
normative for the repaired target; the Lean kernel validates only elaborated
declarations and proof terms. A successful build is not by itself a semantic
alignment result.

Start from the current remote branch, not from an older P5/P3-P4 worktree:

```bash
git fetch origin --prune
git switch -c <p6-branch> origin/main
git status --short --branch
git log -1 --oneline
```

Read without modifying:

```text
AGENTS.md
README.md
lean-toolchain
lakefile.toml
lake-manifest.json
STC.lean
STC/Bootstrap.lean
STC/Foundation/Relation.lean
STC/Foundation/Result.lean
STC/Core/Effect.lean
STC/Core/Partial.lean
STC/Core/Iterator.lean
STC/State/Like.lean
STC/State/Observation.lean
STC/State/RegistryLike.lean
STC/State/FinmapAdapter.lean
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
docs/blueprint/baseline/DeepSeek-Harness-01-Formal-Reference.md
docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.json
docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-08-ADR-04-Incarnation-Identity-and-Alpha-Equivariance-Architecture.json
docs/blueprint/architecture-decision/json/DeepSeek-Harness-10-ADR-06-Equivalence-and-Equivariance-Closure.json
docs/status/P0-baseline.json
docs/status/P3-handoff-report.md
docs/status/P4-handoff-report.md
docs/status/P5-handoff-report.md
docs/status/Definition-Ledger.json
```

The Project Guide and Research Ledger are historical/context documents, not
formalization dependencies. Historical ADR spikes are compiler mirrors only:
do not import, copy, or edit them.

Run the cumulative baseline gate before production edits:

```bash
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
```

The scanner contract is part of the project protocol: exit `1` means clean,
exit `0` means a lexical match requiring inspection, and exit `2` means a scan
error. Missing `lean`/`lake` is `blocked`, not a pass. Verify the H03/H04 and
accepted-ADR hashes against `docs/status/P0-baseline.json`; do not normalize a
recorded provenance mismatch.

The current main tree contains the P3/P4 implementation and the merged
ADR-07–10 packet commits. Those later packets are not P6 implementation
dependencies; they remain architecture/interface inputs for future control,
staging, support, and scoped work.

## 3. Ownership and dependency gates

P6 is one sequential workstream so that the action convention, conjugated
inverse, and iterator transport theorem cannot drift between agents:

```text
P6-PREP API/toolchain audit
   → P6-T01 Alpha/Core action algebra
   → P6-T02 Alpha/Transport result and iterator transport
   → P6-T03 trace/reference and freshness boundary
   → P6-T04 finite evidence and handoff
```

The following paths are integration-owned and are locked during implementation:

```text
STC.lean
STC/Bootstrap.lean
docs/status/Definition-Ledger.json
docs/status/P6-scan-raw.txt
docs/status/P6-handoff-report.md
```

The P6 agent owns only:

```text
STC/Alpha/Core.lean
STC/Alpha/Transport.lean
STC/Examples/Alpha.lean
```

An additional narrowly named `STC/Alpha/Trace.lean` is allowed only if the
trace section makes `Transport.lean` unmanageably large; it must be reported as
a deliberate boundary split and imported only by `Transport.lean`. Do not edit
`STC/Core/Iterator.lean`, `STC/State/**`, `STC/Examples/TwoCounter.lean`, or
`STC/Examples/VerticalSlice.lean`; P7 will extend the latter examples after P6.
The integration owner adds cumulative imports, updates the ledger, records the
scan, and reviews/merges the handoff.

## 4. P6-T01 — alpha action core

Primary file: `STC/Alpha/Core.lean`.

### 4.1 Action carrier and convention

Define one generic action record in the `STC` namespace, using the group action
convention fixed by ADR-06:

```lean
structure AlphaAction (N : Type u) (X : Type v) where
  act : Equiv.Perm N → X → X
  act_id : ∀ x, act (Equiv.refl N) x = x
  act_comp : ∀ (χ ψ : Equiv.Perm N) x,
    act (χ * ψ) x = act χ (act ψ x)
  act_inv : ∀ (χ : Equiv.Perm N) x,
    act χ.symm (act χ x) = x
```

The exact universe parameters may be generalized, but do not change the
composition orientation. Derive the opposite cancellation direction when a
transport proof needs it; do not add a second incompatible action law.

Also define or prove:

- `AlphaInvariant A R`, expressing that the selected relation is preserved and
  reflected by every permutation;
- the conjugated endomorphism `renameUndo A χ f`,
  `z ↦ A.act χ (f (A.act χ.symm z))`;
- identity, composition, inverse/cancellation, and pointwise equations for the
  action and conjugated maps;
- `renameUndo_comp`, with the order matching P2's
  `Transformation.twisted`/P4's reverse inverse accumulation;
- relation-preservation lemmas such as `respects_renameUndo` and the
  pointwise transport of selected inverses under `AlphaInvariant`.

Do not use a global `Setoid`, quotient the state carrier, or infer an action from
an arbitrary equality relation. The action is an explicit reindexing witness.

### 4.2 Existing result carriers

Add tag-preserving actions for the already merged carriers:

```text
EffectResult S
Failure S E
ExecResult S E
StageResult S E Q
```

The state field is mapped by `A.act χ`; each inverse field is mapped by
`renameUndo`; constructor tags are preserved; `E` and `Q` are left unchanged in
this name-neutral profile. Expose equations suitable for rewriting and prove
the action laws that are genuinely needed by the transport file. In
particular, a `raise` branch must not acquire a fabricated state, error, or undo.

The minimum checked API should include equivalents of:

```text
renameEffectResult
renameFailure
renameExec
renameStage
renameUndo_apply
renameUndo_comp
renameExec_id / renameExec_comp / renameExec_inv (or exact equivalents)
```

If a result action requires an equality relation on errors, make that relation an
explicit parameter. The neutral profile may use unchanged errors, but it must
not be presented as a theorem about name-bearing errors.

### 4.3 T01 evidence

The action algebra and result equations are `K` only when their proofs are
checked by the pinned kernel. Definitions without proofs are `I`. The handoff
must list the exact assumptions of every relation theorem, especially
`AlphaInvariant A R.rel`, and must include at least one nontrivial finite action
rather than only the identity permutation.

## 5. P6-T02 — result, iterator, and execution transport

Primary file: `STC/Alpha/Transport.lean`; import the production P4 iterator,
not its historical spike.

### 5.1 Iterator action

For `it : RankedIterator S E Q`, define `renameIterator A χ it` by preserving
`root` and `rank`, and by running the original iterator on the inverse-renamed
state before renaming its result:

```text
runχ q s = renameStage A χ (it.run q (A.act χ.symm s))
```

The construction must preserve the strict-successor certificate using the
existing `it.next_lt`; no new fuel, coinduction, or arbitrary rank adjustment is
allowed. The core equations should include:

```text
renameIterator_run_transport
rank/ root preservation
StageRelC transport under AlphaInvariant
IteratorSimulation transport
IteratorBisim transport (with the converse continuation relation unchanged)
```

Transport the existing `StageInverseProper`, `IteratorInverseProper`,
`StageWitness`, and `IteratorWitness` packages when their relation hypotheses
are explicitly supplied. Do not turn a witness field into an unproved global
law.

### 5.2 Well-founded execution

Prove the name-neutral execution equations over the existing `execFrom` and
`exec`:

```text
execFrom (renameIterator A χ it) q (A.act χ s)
  = renameExec A χ (execFrom it q s)

exec (renameIterator A χ it) (A.act χ s)
  = renameExec A χ (exec it s)
```

The proof must follow the existing rank recursion and preserve the success /
failure tag. In a yielded success branch, the conjugated inverse must compose
in the same outer-after-inner order as P4; in a yielded failure branch, the
boundary and prefix undo must both transport. A `raise` stage carries the
unchanged neutral error and the identity prefix undo exactly as the P4 carrier
specifies.

If Lean's well-founded equation elaboration requires helper lemmas or an
explicit induction measure, keep those helpers local to `Alpha/Transport.lean`
and document the reason. Never replace `execFrom` with a fuel-based duplicate.

### 5.3 Scope of the theorem

The transport theorem is intentionally parameterized by the name-neutral
profile. It is valid only when:

- the state action satisfies the `AlphaAction` laws;
- the selected state relation has an explicit `AlphaInvariant` proof whenever a
  relation-level theorem is claimed; and
- `Q`, `E`/`Xi`, and any continuation/error payload used by the iterator are
  treated as name-neutral.

Do not quantify over an implicit action on `Q` or `E` and then silently use the
identity. A future named-payload profile must supply `RenameQ`, `RenameXi`,
or equivalent actions plus interpreter/run equivariance; that is a deferred
P6-T03 obligation.

## 6. P6-T03 — trace/reference and freshness boundary

Primary file: `STC/Alpha/Transport.lean` (or the explicitly justified
`Alpha/Trace.lean`). This section is an orchestration/trace interface, not a
replacement for P5's abstract state or registry.

### 6.1 Lifetime freshness primitives

Use an abstract name type `N` with only the decidable equality needed by finite
operations. A minimal production shell should expose equivalents of:

```lean
abbrev ParentRef (N : Type u) := Option N

structure NameLedger (N : Type u) [DecidableEq N] where
  everIssued : Finset N

def CurrentFresh (current : Finset N) (n : N) : Prop := n ∉ current
def EverFresh (ledger : NameLedger N) (n : N) : Prop :=
  n ∉ ledger.everIssued
def LedgerSound (current : Finset N) (ledger : NameLedger N) : Prop :=
  current ⊆ ledger.everIssued
```

Keep `CurrentFresh` and `EverFresh` separate. If an allocation helper is
provided, it must return an explicit success/undefined result and update the
ledger monotonically; `none` is not an `ExecResult.failure` unless a caller
supplies a diagnostic, boundary, and prefix undo. Parent permission should be
an explicit predicate over `Option N`; `none` is the synthetic root marker and
does not require a provider entry.

### 6.2 Permutation transport of names and boundaries

Provide an explicit `renameFinset`/equivalent map and transport laws for:

- finite name sets and list allocations;
- `Option N` parent/reference fields, fixing `none`;
- `NameLedger` and `LedgerSound`;
- current/ever freshness and any visible `AllocationAllowed` predicate;
- a product boundary carrying `state : S` and trace metadata.

The product boundary is the place where a freshness-sensitive transition may be
considered Markovian. The default P5 core observation must continue to project
only the state component. If a name-aware boundary relation is exposed, make
its ledger/reference conditions explicit; do not call it alpha equivalence.

### 6.3 Finite-support trace shell

Define a small `NameTrace`/`TraceMeta` record containing, at minimum:

```text
initial issued set
finite boundary snapshots or an explicit boundary envelope
allocation names
parent/reference names
declared finite support envelope
```

Its renaming operation must map every listed name-bearing field. Add a
`TraceSupport` predicate that says the declared support contains the listed
initial, allocation, parent, and reference fields (and any supplied boundary
footprints). A support envelope is not automatically the exact minimal set of
names occurring in a trace; do not prove or imply that equality without an
explicit occurrence-union definition.

Add no-reuse and support transport lemmas for the finite shell. These may be
`K` when proved for the concrete records. A generic operational
`StepEquivariant` relation is allowed only as an explicit contract with visible
before/label/after actions; do not define an always-true or unreachable step
relation merely to discharge a name theorem.

### 6.4 Deliberate boundary exclusions

P6-T03 records, but does not prove:

- exact occurrence-set equality for real lifecycle traces;
- authoritative labelled control constructors and nested-allocation coverage;
- episode/support/precedence reindexing and L68/L70/L72/T73;
- name-bearing `Q`, `Xi`, ambient, accumulator, target-hash, or control-payload
  actions;
- `(runtime atom, generation) → IncarnationId` refinement;
- stale-handle safety for a concrete lifecycle implementation.

These are explicit later obligations (primarily BD-CONTROL, BD-SUPPORT,
BD-SCOPED, and the future runtime-refinement phase), not missing hypotheses to
hide in `WellFormed`.

## 7. P6-T04 — finite alpha evidence

Primary file: `STC/Examples/Alpha.lean`. Keep it independent of the P7 staged
examples so that P6 can be merged without editing `TwoCounter.lean` or
`VerticalSlice.lean`.

Use a genuinely nontrivial finite name action, for example `N := Fin 2` with a
swap permutation and a small state carrying a name plus a reversible bit/value.
The fixture should provide:

1. identity, swap, and inverse action checks;
2. a nontrivial `renameUndo`/result check;
3. a one- or two-stage `RankedIterator` whose renamed execution agrees with
   `renameExec`, including at least one successful result;
4. a separate failure or boundary check showing that the failure tag,
   boundary, and prefix undo are retained under transport;
5. freshness/ledger and no-reuse transport checks;
6. a check that a core-state observation can ignore ledger metadata while an
   explicitly name-aware boundary observation can distinguish it.

Use finite decidable data and `example`/theorem blocks with `by decide` where
kernel reduction supports them. The well-founded `execFrom` may not reduce
under `decide`; in that case pin the expected finite result through its equation
theorems, as P4 does. Do not place top-level `#eval` over exposed production
declarations.

The fixture is evidence (`E`) for the selected finite profile, not a theorem
about all name-bearing iterators or the Cordis runtime.

## 8. Validation and handoff gate

Focused checks, using the repository's explicit Lean options, are:

```bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Alpha/Core.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Alpha/Transport.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Alpha.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
```

The final scanner exit must be `1` (clean), with raw output retained by the
integration owner in `docs/status/P6-scan-raw.txt`. Every focused check and the
cumulative build must finish with zero errors and zero linter warnings. If the
pinned compiler is unavailable, the handoff must say `blocked` and must not
promote interface or theorem evidence based on an unrun command.

The P6 handoff report must record:

- branch, base commit, and exact changed files;
- the action convention and the neutral-payload assumptions;
- theorem inventory classified as `A`, `I`, `K`, `E`, or `R0`;
- exact command outcomes and scanner interpretation;
- finite report values and any equation-pinning workaround;
- deferred named-payload, trace/control, support, and runtime obligations;
- confirmation that frozen baselines, accepted ADR files, P3/P4/P5 modules,
  integration-owned paths, and historical spikes were not modified.

## 9. Ledger coordination (integration owner only)

The P3/P4/P5 handoff reports contain derived ledger patches that were not part
of their production branches. Before applying a P6-specific patch, the
integration owner must reconcile those cumulative patches against the current
`origin/main`; the frozen H03/H04 files and dependency lists remain unchanged.
The P6 agent must not edit `Definition-Ledger.json` while implementing the
alpha modules.

After a successful P6 handoff, the likely derived updates are deliberately
granular (exact statuses depend on the checked theorem inventory):

| Row | Possible P6 update | Boundary that remains visible |
|---|---|---|
| `D45` | retain `in_progress/seam_only`; add the explicit freshness-boundary note | provider adequacy and active-store semantics remain deferred |
| `D53` | `in_progress/seam_only` for the trace/name boundary | lifecycle/control trace decomposition remains BD-CONTROL |
| `L56` | `in_progress/proved` for the name-neutral transport theorem, if the kernel checks it | named `Q`/`Xi`/payload variant remains deferred |
| `D60` | retain the P4 transport/iterator evidence | reach-closed lifecycle monoid remains BD-CONTROL |
| `T73` | no completion claim; at most add alpha-support evidence | support/confluence remains BD-SUPPORT + BD-CONTROL |
| `D65`, `L68`, `L71`, `L72` | no completion claim from P6 alone | precedence, support, and adjacent transposition/deletion proofs remain later work |

Do not remove `BD-CONTROL`, `BD-SUPPORT`, `BD-STAGING`, or `BD-SCOPED` merely
because a generic alpha action compiles. A production declaration earns `I`
or `K` according to its actual proof; a boundary contract earns `R0` only when
it is an explicit abstraction/refinement interface.

## 10. Reopen rules and downstream order

P6 may refine theorem names or split a trace companion without a new ADR if the
accepted carriers, action orientation, and ledger boundary are preserved. Any
change to one of these requires a superseding decision packet:

- replacing the raw state or observation carrier;
- treating alpha equivalence as the default observational relation;
- changing the selected inverse or failure meaning;
- putting freshness into `RawState`/default `CoreStateObs`;
- making a deterministic allocator part of the generic alpha theorem;
- claiming named-payload or runtime-refinement equivariance without an explicit
  action and law.

The intended downstream order is:

```text
P6 alpha transport
  → P7 complete TwoCounter vertical slice
  → control/staging integration (ADR-07/08)
  → support/well-foundedness integration (ADR-09)
  → scoped coeffect integration (ADR-10)
  → P8 conformance and R0/R1+ refinement
```

P6 therefore closes a useful name-neutral transport layer, but it does not
close L56 or T73 in their full paper-facing forms until the later control,
support, and payload semantics are present.
