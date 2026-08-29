# STC P13 Global Metatheory Execution Plan

| Field | Value |
|---|---|
| Plan ID | `DH-P13-GLOBAL-METATHEORY-EXEC-01` |
| Repository | https://github.com/eiKeViN/DeepSeek-STC |
| Prepared | 2026-08-29 |
| Planning baseline | `origin/main` at `ad77875`, after the P11 integration merge and P12 post-join integration |
| Depends on | accepted ADR-01--10 architecture; P9 accepted-status records for ADR-07/08/09/10; P10 Control; P11 Staging/Support/integration; P12 Scoped |
| Scope | old-paper, single-realm Section-4 production semantics and repaired global metatheory; required transitive prerequisite closure; derived P13 conformance manifest |
| Execution shape | serial foundation/API freezes, five proof lanes, two theorem joins, one central integration owner |
| Status | ready to schedule after this plan is merged and the fresh integrated build gate passes |

P13 may now be planned: P11 and P12 are both present on `origin/main`, the
Definition Ledger validates all 82 rows, and the accepted architecture records
are closed. That does **not** make P13 a direct proof of T73. The current
repository has reusable Control, Staging, Support, Alpha, Iterator, State, and
Scoped interfaces, but it still lacks the concrete Section-4 state, the
guarded semantics for the ten printed rule cases, reached states, episodes,
and rule-level factorization on which the global theorems depend.

This plan therefore has four major joins:

1. close the twelve real transitive prerequisites and freeze a positive,
   data-only Section-4 state API;
2. implement and freeze one authoritative calculus covering the paper's three
   orchestration and seven printed lifecycle cases, plus
   reachability and episodes;
3. run the structural, recovery, support, spatial/progress, and alpha/
   commutation proof lanes;
4. join them into closed-episode deletion and the repaired canonical-form/
   confluence package.

The formal target remains the audited old paper and H04 repairs used by the
existing repository. The newer arXiv version is not reconciled in P13. P12's
Scoped layer is included in final conformance accounting, but it is not
silently used to turn the old paper's single-realm Section-4 theorems into
realm-aware theorems.

## 1. Verified entry state

The planning audit found this ancestry on `origin/main`:

~~~text
0461596  P11 integration delivery
7b1d0e3  merge of the P11 integration lane
a276fbb  P12 Scoped delivery
ad77875  P12 Bootstrap and Definition Ledger post-join integration
~~~

The relevant handoffs are:

~~~text
docs/status/P10-api-freeze.md
docs/status/P10-handoff-report.md
docs/status/P11-staging-handoff-report.md
docs/status/P11-support-core-handoff-report.md
docs/status/P11-integration-handoff-report.md
docs/status/P12-scoped-handoff-report.md
~~~

At planning time:

* `python scripts/validate_definition_ledger.py
  docs/status/Definition-Ledger.json` passes 82/82 and verifies the frozen
  H03/H04 hashes;
* `python scripts/scan_lean.py STC` exits 1, meaning clean;
* the planning worktree passes `git diff --check`;
* D28--D31 are `completed/proved`, and Bootstrap imports the P12 production
  and example umbrellas;
* the stored P11 and P12 handoffs report successful focused Lean checks and
  builds.

No compatible `lake`/`lean` executable or dependency checkout was available
in the planning environment. In particular, the integrated `ad77875` default
Bootstrap closure has not been freshly built by this planning run. A fresh
integrated build is therefore a hard P13 execution gate, not an inherited
assumption.

The P12 handoff records a stale branch-base hash (`69b4184`), whereas Git
records `7b1d0e3` as the parent of `a276fbb`. Do not rewrite that historical
handoff. Record the actual ancestry in the P13 handoff.

## 2. Authority and theorem boundary

Four kinds of statement must remain distinct:

1. a literal claim in the archived paper;
2. its frozen H03 dependency and H04 disposition/repair;
3. the production target accepted by ADR-07 through ADR-10;
4. a Lean theorem whose complete premises and proof have been kernel checked.

P13 targets architecture (`A`), production integration (`I`), checked theorem
evidence (`K`), and finite positive/negative evidence (`E`). It may inventory
the existing abstract/runtime seam (`R0`), but it does not establish Cordis
refinement (`R1+`). Compilation alone is `I`; a structure field assuming a law
is a contract/seam, not `K` evidence for that law.

The following repaired targets are normative:

* ADR-07: orchestration and lifecycle remain distinct relation classes;
  `Step`/`Trace` preserve labels and endpoints; async landing/abort and failure
  payloads are explicit; there is no scheduler or hidden fairness assumption.
* ADR-08: the extended calculus covering the printed 3+7 rule cases is
  authoritative. `R.base` is only a
  derived finite macro/view through Staging, never a second independently
  maintained calculus.
* ADR-09: `SupportRel` is oriented provider/parent to dependent, `SupportDep`
  is its converse for induction, `SupportSet` is the existing positive least
  fixed point, and every support rank/order certificate remains explicit.
* ADR-10: P12 supplies scoped primitives and a one-way flat embedding. It does
  not authorize an arbitrary scoped-to-flat projection or a realm-aware
  generalization of T63/L70/T73.

Do not identify the repository's distinct relations by notation or prose.
Transformation equivalence, D33 state observation, action/result equivalence,
D53 episode/control-edit equivalence, and alpha renaming need separately named
definitions and explicit bridge theorems. No proof may silently rewrite one
into another.

The paper-level repairs that matter most in P13 are:

* T61's strongest "as if the fiber never began" form requires an explicit
  no-registered-child-steps restriction; the general theorem remains modulo
  the stated D53 observational relation.
* T64 must state the independence/continuation-stability hypotheses inherited
  from C62.
* T66 begins at an arbitrary suitably reached state and concerns its
  lifecycle-only suffix. It must not use the vacuous claim that an entire
  trace from the empty registry is lifecycle-only.
* literal L68 is false. P13 must mechanize the semantic counterexample and
  prove the corrected restricted theorem under an explicit no-late/committed
  support invariant.
* L70 must derive the active-set fixed-point equation from semantic premises;
  it may then reuse the P11 algebraic fixed-point theorem.
* L72 must expose the complete recovery, independence, support, quiescence,
  nonfailure, and total-provision envelope.
* T73 is split into canonicalization and confluence at quiescent endpoints,
  followed by a separate unique-normal-form corollary that additionally uses
  T66 termination.

## 3. Preflight and branch gate (`P13-T00`)

Create the execution branch from the commit containing this plan. The actual
branch base must descend from all four milestones below; record it rather than
copying the planning hash mechanically.

~~~bash
git fetch origin --prune
git switch -c <p13-execution-branch> origin/main
git status --short --branch
git log -1 --oneline

git merge-base --is-ancestor 0461596 HEAD
git merge-base --is-ancestor 7b1d0e3 HEAD
git merge-base --is-ancestor a276fbb HEAD
git merge-base --is-ancestor ad77875 HEAD

python scripts/prepare_worktree_lake.py

for adr in 07 08 09 10; do
  jq -e '
    .record_status == "accepted" and
    .architecture_status == "closed" and
    .formal_acceptance == true
  ' "docs/blueprint/architecture-decision/status/ADR-${adr}-accepted.json"
done

python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
git diff --check
~~~

All ancestry, acceptance, Lean, build, Ledger, and diff gates must pass before
implementation begins. For `scan_lean.py`, exit 1 means clean, exit 0 means
lexical matches requiring classification, and exit 2 means scanner failure.
An unavailable compiler or failed integrated build blocks P13; do not inherit
"passed" from a previous handoff.

Read before editing:

~~~text
AGENTS.md
README.md
STC.lean
STC/Bootstrap.lean
STC/Control.lean
STC/Control/Support.lean
STC/Staging.lean
STC/Staging/Support.lean
STC/State/Support.lean
STC/State/Support/Closure.lean
STC/State/Support/Alpha.lean
STC/Alpha/Core.lean
STC/Alpha/Trace.lean
STC/Alpha/Transport.lean
STC/Core/Effect.lean
STC/Core/Partial.lean
STC/Core/Iterator.lean
STC/State/CoeffectStore.lean
STC/State/Like.lean
STC/State/Observation.lean
STC/State/RegistryLike.lean
STC/State/FinmapAdapter.lean
STC/Scoped.lean
docs/status/Definition-Ledger.json
docs/status/P11-integration-handoff-report.md
docs/status/P12-scoped-handoff-report.md
docs/status/P0-baseline.json
docs/blueprint/baseline/DeepSeek-Harness-01-Formal-Reference.md
docs/blueprint/baseline/DeepSeek-Harness-03-Definition-Theorem-Dependency-Graph.md
docs/blueprint/baseline/DeepSeek-Harness-04-Formalization-Disposition-Specification.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
docs/blueprint/architecture-decision/md/DeepSeek-Harness-07-ADR-03-BD-STATE-Closure-Packet.md
docs/blueprint/architecture-decision/md/DeepSeek-Harness-08-ADR-04-Incarnation-Identity-and-Alpha-Equivariance-Architecture.md
docs/blueprint/architecture-decision/md/DeepSeek-Harness-09-ADR-05-Iterator-and-Failure-Architecture.md
docs/blueprint/architecture-decision/md/DeepSeek-Harness-10-ADR-06-Equivalence-and-Equivariance-Closure.md
docs/blueprint/architecture-decision/md/DeepSeek-Harness-12-ADR-07-Control-Architecture.md
docs/blueprint/architecture-decision/md/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture.md
docs/blueprint/architecture-decision/md/DeepSeek-Harness-14-ADR-09-Support-Well-Foundedness-Architecture.md
docs/blueprint/architecture-decision/md/DeepSeek-Harness-15-ADR-10-Scoped-Coeffect-Architecture.md
~~~

After the fresh build passes, reconcile only the **live** current-status prose
that still calls P12/Scoped pending in README, AGENTS, and the executable
Blueprint Markdown/JSON. Preserve dated snapshots. Do not edit the P12 handoff,
frozen baselines, candidate ADRs, accepted status records, or historical P8
manifest. Commit the entry/status reconciliation before code lanes branch.

## 4. Ownership and protected surfaces

P13 should prefer additive companion modules. The planned production surface
is:

~~~text
STC/Core/Effect/Closure.lean
STC/Core/Partial/Recovery.lean
STC/Core/Coeffect.lean
STC/Foundation/Relation/Transport.lean
STC/State/Positive.lean
STC/State/Observation/Lift.lean
STC/State/Component.lean
STC/State/Fiber.lean
STC/State/Global.lean
STC/State/Global/Observation.lean
STC/Control/Rules.lean
STC/Control/Reachability.lean
STC/Control/Structural.lean
STC/Control/Preservation.lean
STC/Control/Recovery.lean
STC/Control/Spatial.lean
STC/Control/Progress.lean
STC/Control/Support/Reachable.lean
STC/Control/Support/Quiescence.lean
STC/Control/Alpha.lean
STC/Control/Commutation.lean
STC/Control/Episode.lean
STC/Control/Deletion.lean
STC/Control/Canonical.lean
STC/Conformance/Global.lean
STC/Examples/PrerequisiteRecovery.lean
STC/Examples/PrerequisiteCoeffect.lean
STC/Examples/PrerequisiteState.lean
STC/Examples/GlobalModel.lean
STC/Examples/GlobalRules.lean
STC/Examples/GlobalStructural.lean
STC/Examples/GlobalRecovery.lean
STC/Examples/GlobalProgress.lean
STC/Examples/GlobalAlpha.lean
STC/Examples/GlobalDeletion.lean
STC/Examples/GlobalConfluence.lean
STC/Examples/Global.lean
STC/Examples/SupportCycle.lean
~~~

The path split above is part of the ownership contract. A consolidation or
rename requires a recorded pre-freeze reopen that also updates the ownership
matrix and every validation path in this plan. No lane may consolidate files
unilaterally or create competing state, trace, support, or relation families.

Only the central integration owner edits shared artifacts:

~~~text
STC/Bootstrap.lean
README.md
AGENTS.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
docs/status/Definition-Ledger.json
docs/status/P13-api-freeze.md
docs/status/P13-conformance-manifest.json
docs/status/P13-handoff-report.md
docs/status/P13-scan-raw.txt
~~~

The following merged APIs are byte-for-byte protected by default:

~~~text
STC.lean
STC/Control.lean
STC/Control/Support.lean
STC/Staging.lean
STC/Staging/Support.lean
STC/State/Support.lean
STC/State/Support/Closure.lean
STC/State/Support/Alpha.lean
STC/Alpha/**
STC/Core/Effect.lean
STC/Core/Partial.lean
STC/Core/Iterator.lean
STC/Foundation/Relation.lean
STC/State/CoeffectStore.lean
STC/State/Like.lean
STC/State/Observation.lean
STC/State/RegistryLike.lean
STC/State/FinmapAdapter.lean
STC/Scoped.lean
STC/Scoped/**
STC/Examples/Control.lean
STC/Examples/Staging.lean
STC/Examples/Support.lean
STC/Examples/SupportTrace.lean
STC/Examples/Scoped.lean
STC/Conformance/Manifest.lean
~~~

If an additive module cannot express a required theorem because a needed
declaration is private or an accepted signature is inconsistent, stop and
report the smallest required upstream API change. Do not opportunistically
edit a protected carrier.

Always protected:

~~~text
docs/blueprint/baseline/**
docs/blueprint/architecture-decision/md/**
docs/blueprint/architecture-decision/json/**
docs/blueprint/architecture-decision/lean-spike/**
docs/blueprint/architecture-decision/status/**
docs/status/P8-conformance-manifest.json
~~~

The P13 manifest uses a new generator and a new output path. Never run the P8
generator or overwrite the historical P8 manifest.

## 5. Required data and import architecture

The concrete state must remain positive. A registry cell may store component,
iterator, accumulator, landing, undo, and failure **codes/data**, but it may not
store a closure of type `RawState -> RawState`, `RawState -> Prop`, a
`RankedIterator RawState ...`, or an `InFlight` whose state parameter is the
containing raw state. Denotations and refinement laws live in an external
semantic profile. This prevents the rejected negative cycle
`State -> Registry -> Fiber -> (State -> State)`.

Use an acyclic module graph equivalent to:

~~~text
Effect closure + partial recovery + coeffect/SAT + relation transport
                              |
                              v
              Component/Fiber data-only carriers
                              |
                              v
 Global state, observations, provider/active views, WF, allocation history
                              |
                              v
 authoritative guarded rules for all printed cases and derived family views
                              |
                              v
             reached states, traces, episodes, factorization
                 /          |          |          \
                v           v          v           v
       structural/WF    recovery    support    alpha/commutation
                \           |          |           /
                 +----------+----------+----------+
                              |
                    spatial/progress joins
                              |
                 closed-episode deletion (L72)
                              |
             canonicalization/confluence (T73)
                              |
              finite evidence + P13 conformance
~~~

Existing generic files remain lower layers. Support Core must remain usable
without importing Control, Staging, or Scoped. Production modules never import
examples, conformance artifacts, or historical spikes.

The global state must retain immutable allocation order (`issuedAt`, birth
index, or an equivalent ordered allocation history) in addition to
`NameLedger.everIssued`. A `Finset` of issued names alone cannot recover the
`SupportSnapshot.birth` function. Freshness is lifetime-based, not merely
fresh among currently live registry keys.

## 6. Task graph and scheduling

~~~text
P13-T00  fresh integrated build + live-status reconciliation
   |-- P13-T01A  effect closure/recovery prerequisites --+
   +-- P13-T01B  coeffect/SAT prerequisites ------------+
                                                        v
 P13-T01C -> P13-T02 -> P13-T03 -> P13-T04 semantic freeze
                                             |
                 +---------------------------+--------------------------+
                 v                           v                          v
           P13-T05A                    P13-T05B                 T05C/D/E starts
                 +---------------------------+--------------------------+
                                             v
                                  T05C/D/E final joins
                    T05A + T05B + T05C -> P13-T06 (L72)
       all T05 lanes + T06 -> P13-T07 -> P13-T08 -> P13-T09 -> P13-GATE
~~~

T01A and T01B are disjoint and may run in parallel. After the T04 API freeze,
all five T05 lanes may start, but their final claims have these joins:

* T05B's T64 result waits for the recovery hypotheses and T05A structural
  facts;
* T05C may build the state projection and counterexample immediately, but
  concrete trace preservation and L70 wait for T05A/T59;
* T05D's T63 waits for T05A, and T66 additionally consumes the completed D60
  lifecycle measure from T05B;
* T05E's alpha transport may start immediately, while L71 waits for T05A and
  the continuation-stability/independence results from T05B;
* T06 waits for T05A, T05B, and T05C; T07 waits for every T05 lane and T06.

The exact start/completion joins are:

| Task/lane | May start after | May claim complete after |
|---|---|---|
| T01A, T01B | T00 | its own focused gate |
| T01C | T01A and T01B | abstract interfaces and L38 gate |
| T02, T03, T04 | prior serial task | central freeze checkpoint/build |
| T05A | T04 | its own focused gate |
| T05B | T04 | T05A for T64; otherwise its recovery gate |
| T05C | T04 | T05A/T59 for certificate preservation and L70 |
| T05D | T04 | T05A for T63 and T05B/D60 for T66 |
| T05E | T04 | T05A and T05B for L71 |
| T06 | T05A, T05B, T05C | constructed shortened-trace gate |
| T07 | all T05 lanes and T06 | three-result T73 gate |
| T08 | T07 | finite/schema/generator gate |
| T09 | T08 | final integrated validation |

Each lane owns disjoint new module/example paths:

| Task | Exclusive code/evidence paths | Lane record |
|---|---|---|
| T01A | `STC/Core/Effect/Closure.lean`; `STC/Core/Partial/Recovery.lean`; `STC/Examples/PrerequisiteRecovery.lean` | `docs/status/P13-lanes/T01A-handoff.md` |
| T01B | `STC/Core/Coeffect.lean`; `STC/Examples/PrerequisiteCoeffect.lean` | `docs/status/P13-lanes/T01B-handoff.md` |
| T01C | `STC/State/Positive.lean`; `STC/State/Observation/Lift.lean`; `STC/Foundation/Relation/Transport.lean`; `STC/Examples/PrerequisiteState.lean` | `docs/status/P13-lanes/T01C-handoff.md` |
| T02 | `STC/State/Component.lean`; `STC/State/Fiber.lean`; `STC/State/Global.lean`; `STC/State/Global/Observation.lean`; `STC/Examples/GlobalModel.lean` | `docs/status/P13-lanes/T02-handoff.md` |
| T03 | `STC/Control/Rules.lean`; `STC/Examples/GlobalRules.lean` | `docs/status/P13-lanes/T03-handoff.md` |
| T04 | `STC/Control/Reachability.lean`; `STC/Control/Episode.lean` | `docs/status/P13-lanes/T04-handoff.md` |
| T05A | `STC/Control/Structural.lean`; `STC/Control/Preservation.lean`; `STC/Examples/GlobalStructural.lean` | `docs/status/P13-lanes/T05A-handoff.md` |
| T05B | `STC/Control/Recovery.lean`; `STC/Examples/GlobalRecovery.lean` | `docs/status/P13-lanes/T05B-handoff.md` |
| T05C | `STC/Control/Support/Reachable.lean`; `STC/Control/Support/Quiescence.lean`; `STC/Examples/SupportCycle.lean` | `docs/status/P13-lanes/T05C-handoff.md` |
| T05D | `STC/Control/Spatial.lean`; `STC/Control/Progress.lean`; `STC/Examples/GlobalProgress.lean` | `docs/status/P13-lanes/T05D-handoff.md` |
| T05E | `STC/Control/Alpha.lean`; `STC/Control/Commutation.lean`; `STC/Examples/GlobalAlpha.lean` | `docs/status/P13-lanes/T05E-handoff.md` |
| T06 | `STC/Control/Deletion.lean`; `STC/Examples/GlobalDeletion.lean` | `docs/status/P13-lanes/T06-handoff.md` |
| T07 | `STC/Control/Canonical.lean`; `STC/Examples/GlobalConfluence.lean` | `docs/status/P13-lanes/T07-handoff.md` |
| T08 | `STC/Conformance/Global.lean`; `STC/Examples/Global.lean`; `scripts/generate_p13_conformance_manifest.py` | `docs/status/P13-lanes/T08-handoff.md` |

Lane records are tracked artifacts owned by their lane. They contain the exact
base/head, changed-path allowlist, public API or theorem inventory, focused
commands/exit codes, negative/nonvacuity evidence, and proposed Ledger deltas.
They do not edit the central Ledger, Bootstrap, live guidance, API-freeze
record, final P13 handoff, scan record, or manifest output.

A named central freeze owner merges T02, T03, and T04 in order and updates
`docs/status/P13-api-freeze.md` after each checkpoint. Each checkpoint records
the merge commit, public signatures, module-file SHA-256 hashes, focused checks,
and full-build result. The freeze covers carrier/rule/episode signatures;
later proof modules are additive consumers. No signature may change after its
checkpoint without a coordinated reopen recorded in both the freeze report and
final handoff.

## 7. `P13-T01A` — effect closure and recovery prerequisites

Close D17, L18, T20, and C21 in additive modules over the frozen P2--P4 APIs:

* define the generated transformation submonoid/closure required by D17;
* prove generator membership, identity, composition closure, and the exact
  forward/reverse composition laws;
* prove L18 generator commutation and closure under composition with every
  independence premise explicit;
* prove selective removal of an earlier operation across a later independent
  suffix (T20);
* derive arbitrary-order recovery (C21) rather than restating it as a field.

Keep T20/C21 at their audited core effect/removal strength; do not strengthen
them with lifecycle continuation-stability obligations. The
map-commutes-but-continuation-changes counterexample belongs to T05B/T05E,
where it is used for recovery and transposition.

Do not edit `STC/Core/Effect.lean` or `STC/Core/Partial.lean`; add companion
modules and import their public APIs. The gate is focused elaboration plus a
nonempty recovery fixture containing at least two independent operations.

## 8. `P13-T01B` — coeffect and satisfaction prerequisites

Close D22--D25 and SAT at exactly the strength consumed by the global state:

* complete finite dependent-store domain, union, disjointness, support, and
  lookup algebra over the existing authoritative P5 store;
* define legal witnessed get/set/provide/revoke partial transitions and their
  frame/restoration laws;
* define a typed key-local coeffect interface and context lift with explicit
  relation-respect laws;
* keep semantic specifications distinct from finite executable checkers;
* define SAT semantically, implement the finite checker, and prove checker
  soundness/completeness under its stated decidability/finite-support premises.

No deterministic checker may be called identical to a relational source
specification without an adequacy theorem. No second mutable store is allowed.
This task may run in parallel with T01A.

## 9. `P13-T01C` — abstract positive context/observation join

Deliver the generic contracts needed by D32/D33 and close the
downstream-required part of L38:

* expose a positive, registry-cell-parametric context/state construction
  through the existing Finmap/RegistryLike abstractions, without referring to
  the not-yet-defined D43 component or claiming runtime refinement;
* define the parametric observation kit used by L55, T61, L71, and T73,
  including registry and committed-store observation and extension points for
  lifecycle, control-edit, and name observations;
* prove the small relation-parametric transport/compatibility family that
  subsumes L38 and is actually used downstream.

T02 instantiates this generic carrier and observation kit with the concrete
FiberCell, delivers the D32 representation theorem and the D33 lifted
full-state relation, and owns their final completion evidence. Do not define a
placeholder FiberCell here merely to make the dependency order look complete.

Do not collapse D33 observation, D53 episode equivalence, action/result
equivalence, or alpha renaming. Every conversion is a named lemma with explicit
premises.

The T01 join is complete when T01A/T01B and L38 have checked declarations and
the D32/D33 generic interfaces needed by T02 are frozen. The T02 API freeze is
the gate at which all twelve transitive prerequisites below must have complete
downstream-usable declarations rather than assumptions:

~~~text
D17 L18 T20 C21 D22 D23 D24 D25 SAT D32 D33 L38
~~~

D26, D34/L35, D39/T40, and D41/T42 are not in the P13 transitive closure and
are not silently absorbed into this task.

## 10. `P13-T02` — positive production state and model API freeze

Implement the concrete, data-only Section-4 carrier and freeze its public API.
This task first closes D32/D33 by instantiating the T01C carrier/observation
interfaces, then owns D43--D50 and D58 at the carrier/semantic-profile level;
D47's transition theorem and D48's concrete rule-confinement proofs are
completed by T03.

Required surface:

* D43 Component: requirements, declared provisions, action/iterator codes, and
  an external interpretation contract with the explicit
  no-write-outside-provision obligation;
* D44/D49 FiberCell: incarnation identity, parent, immutable birth/allocation
  index, declarations, local committed data, retired flag, lifecycle phase,
  coded iterator/accumulator/flight payload, and failure/outcome data;
* D45 GlobalState: finite registry, ambient/coeffect store, lifetime name
  ledger, ordered allocation history, and derived active-store fold;
* provider relation and executable `providerOf` with well-formed-relative
  soundness, completeness, and uniqueness;
* D46 target and quiescence views plus the stable-image projection used by
  Staging;
* D48 separate write-frame and read-noninterference predicates/profile-law
  obligations plus pure state-update lemmas, rather than folding them into
  D43; T03 proves concrete stage/O-Insert conformity;
* D50 relied-upon relation over installed fibers and committed provider views;
* D58 WellFormed with parent closure and acyclicity, table confinement,
  provision disjointness, lifecycle coherence, committed-view/provider
  closure, root, and declaration conditions visibly separate.

The semantic interpreter for component/stage/iterator/undo codes is external
to GlobalState and must expose frame, inverse, relation-respect, rank, and
continuation-stability laws. A rule may consume those laws later; it may not
store a raw-state closure in a cell.

Freeze the theorem profiles required downstream rather than asking proof lanes
to invent them:

* every name-bearing component, behavior, iterator, accumulator, in-flight,
  failure, and control code is either explicitly name-neutral or carries an
  alpha action with interpreter-equivariance laws;
* a factorization interface supplies a replayable selected body map/control
  edit and frame law, or an explicitly relational factorization; a constant
  function returning the already-known successor is forbidden as vacuous;
* a progress profile gives begin/iter/finish/cleanup existence, a structurally
  defined `LifecycleReady` invariant, and landing-or-boundary-abort totality;
  `LifecycleReady` may not be defined as `HasLifecycleSuccessor`;
* a confluence profile gives successful-result determinism modulo D33,
  result/continuation coherence, and async landing coherence. Alternatively,
  later confluence inputs must retain the same resolved semantic witnesses.

These profiles are explicit premises where the unrestricted relational model
does not imply them. Without the confluence profile or same-witness input
relation, T73 is false even for successful, nonfailed components with identical
orchestration inputs.

`WellFormed` must not contain `SupportOrder`, `SupportWF`, the theorem to be
proved, or an equivalent hidden certificate. Allocation/birth data is ordinary
state data; the restricted support theorem later proves when it induces a
valid order.

Freeze the exact module graph, public declarations, relation directions, and
projection types in `docs/status/P13-api-freeze.md`. Run focused checks and a
full build before T03 begins. Any later carrier change reopens T02 and all
dependent lanes.

## 11. `P13-T03` — authoritative guarded rule families

Define one concrete rule family over the T02 state, covering:

* the three printed orchestration cases: insert, retire, remove;
* the seven printed lifecycle cases: begin, iter, finish, divert, raise,
  leave, unload;
* an authoritative `ControlModel` instance and typed `Step`/`Trace` reuse;
* explicit guards, selected owner, witnesses, exact successor equations,
  static/write frames, name-ledger changes, and lifecycle/control edits for
  every constructor.

The printed count is not a datatype-arity constraint. In particular, an
implementation may use separate typed landing and abort constructors beneath
the printed Divert case, as H04 permits. Both branches must remain visible and
inhabited, and the mapping from concrete constructors to printed cases must be
derived.

Resolve the H03 `D49 <-> R.iter <-> R.fail` cycle structurally: define all
lifecycle/failure data first, then the guarded constructors, then derive
withdrawal, iteration, and failure subfamily views. Do not implement competing
relations.

Required rule-family outcomes:

* `R.full` is the single authoritative union;
* `R.withdraw`, `R.iter`, and `R.fail` are constructor views with concrete
  guard/frame theorems;
* A.async is an explicit admissible trace/landing policy with sound landing
  and boundary abort; pending/failing paths are not reclassified as success;
* `R.base` is derived only through `Staging.MacroPath`/adequacy over the full
  relation, including profile-tagged stuttering where permitted;
* nested registration consumes an ever-fresh incarnation, returns explicit
  action/inverse witnesses, and preserves the required static/frame fields;
* every allocation/registration is an explicit orchestration insertion with a
  name-ledger/allocation-history update; lifecycle rules cannot allocate a
  name or grow the registry domain;
* every constructor supplies the T02 replay/factorization witness or its
  relational counterpart, including nonconstant replay and frame facts;
* the actual component-stage and O-Insert rules discharge the T02 D48
  write-frame/read-noninterference obligations; T05A later aggregates the
  per-constructor structural facts;
* rule decomposition facts are derived by cases. Table1 is never introduced
  as an axiom or independent truth source.

Before freezing, provide an inhabited witness for every concrete constructor,
every printed rule case, and both Divert branches. At least one fixture must
use two distinct acting fibers, a nonempty requirement and provision, nested
registration, async diversion, and real raise/cleanup.
The state change must be nontrivial except for a separately tagged/authorized
Staging stutter.

At this checkpoint construct only the ADR-09 raw rule-valid cycle-trace
candidate. T04 supplies `Initial`/semantic reachability and T05C proves the
actual counterexample. If the concrete rules cannot realize the candidate,
stop and identify the first impossible step rather than presenting an
arbitrary graph as a reachable counterexample.

Freeze the concrete rule constructors, labels, endpoints, guard vocabulary,
and subfamily projections in the P13 API-freeze report. T04 and all proof lanes
branch only after a focused check and full build.

## 12. `P13-T04` — reachability, episodes, and factorization

Complete D53 over the authoritative rules:

* define initial states without making "empty" the only source of generic
  reachability;
* define `ReachedFrom`, initial reachability, labelled trace segments, actor
  projection, incarnation-indexed open/closed episodes, and episode endpoints;
* define state-map, control-edit, and trace/episode equivalence separately;
* factor each rule through the T02/T03 replayable witness into its selected
  state-map/control-edit components, or prove the frozen relational
  factorization; never use a constant-after-state map;
* prove trace append/split, episode extraction, endpoint, label/input-sequence,
  and no-reuse facts;
* define `SameOrderedOrchestrationInputs`: only ordered orchestration labels,
  payloads, parent references, and freshly allocated names (through a growing
  bijection) are retained. Literal name-bearing label-list equality is too
  strong, while erasing names/payloads is too weak;
* separately define `SameResolvedSemanticWitnesses` for internal action,
  iterator, landing, and nondeterministic resolution witnesses; do not hide
  this stronger restriction inside the external-input relation;
* expose the registered-child-step predicate needed by the strong recovery and
  deletion theorems.

The initial-state profile must make activation provenance explicit. The
standard source has every initial fiber inactive/unstarted. A nonempty source
with an initially active fiber must carry a valid finish/commit certificate.
Define and preserve an `ActivationProvenance` invariant so L70 never invents a
past finish absent from the trace.

Reached state must mean existence of an actual `Control.Trace`; it must not
bundle future preservation, termination, a support certificate, or the theorem
being proved. Initial-empty traces remain useful finite fixtures, while T66
quantifies over an arbitrary state reached by an orchestration prefix.

The end of T04 is the final semantic API freeze. All five T05 proof lanes use
this exact state/rule/episode surface. Changes after this point require a
coordinated reopen, not lane-local patches.

## 13. `P13-T05A` — structural, observation, and preservation

Deliver L54, L55, L57, and T59:

* derive every rule's write footprint, registry edit, lifecycle edit, name
  allocation/retirement behavior, and untouched projections by constructor
  cases (L54 and the machine-derived Table1 artifact);
* prove same-label applicability in both directions and related successor
  existence/bisimulation for D33 observation, preserving the typed label and
  making nondeterministic witnesses explicit (L55); the converse may be a
  separately named theorem or a checked derivation through D33 symmetry;
* prove vestigial-entry equivalence, preservation, and deletion sublemmas
  without erasing a relied-upon/active/parent-referenced entry (L57);
* prove one-step WellFormed preservation from actual rule guards and semantic
  profile laws, then lift it by trace induction (T59).

It is invalid to place `WellFormed after` in every rule constructor and then
call its projection T59. Rule premises may expose local frame/semantic laws;
the global invariant must be derived.

Once the constructor decomposition exists, Table1 may move from
`deferred/deferred` to `completed/proved` while retaining its frozen
`SUBSUMED` treatment. It remains a derived inventory, not an axiom used to
prove L54.

## 14. `P13-T05B` — lifecycle transformation, recovery, and coherence

Complete D60, T61, C62, and T64:

* connect begin/iter/finish/divert/raise traces to the existing ranked
  iterator and result semantics;
* expose the successful-stage graph, its reflexive-transitive `Reach`,
  separately named continuation-reachability, and bounded-length lemmas, not
  merely finiteness of a stored trace;
* use ADR-05's `UniformlyBounded iterator K` boundary (rank-derived where
  applicable) and retain failure/partial branching in the relational graph;
* expose a transformation monoid only for an explicitly total,
  deterministic, nonfailing specialization, then define
  incarnation-indexed independence at the appropriate relational/general
  level using the completed D17/L18 foundation;
* prove episode recovery modulo the correct D53 relation, including inverse
  replay, continuation stability, async land/abort, and failure cleanup (T61);
* state and prove the stronger "as if never begun" variant only under the
  explicit absence of registered-child steps;
* derive terminal recovery for closed/removed fibers (C62);
* prove resolution coherence (T64) with every inherited pairwise independence
  and continuation-stability premise explicit.

Finite `Trace` length does not establish termination, and an abstract inverse
field does not by itself prove recovery. Do not totalize failure or choose one
nondeterministic branch merely to manufacture a monoid. Include success,
diversion, failure, and a rejected overlapping/continuation-unstable example.

## 15. `P13-T05C` — reachable support and quiescence

Complete D65, D67, the repaired L68, D69, and L70:

1. define the exact GlobalState-to-`SupportSnapshot` projection for domain,
   retired names, parent, requires, provides, and immutable birth;
2. prove that projected `Precedes`, `SupportRel`, `SupportDep`, operator, and
   positive least fixed point agree with the production registry (D65/D67);
3. mechanize the actual reachable L68 counterexample under the full rules;
4. define a visibly named safe/no-late rule profile using only a local edit
   guard, equivalent in shape to
   `SafeStep e s t := R.full e s t /\ LocalNoLateEdit e s t`; the local guard
   checks newly introduced parent/precedence edges against immutable birth
   indices;
5. prove `SafeStep -> R.full`, show an inhabited nonempty safe trace, identify
   the first unrestricted counterexample step rejected by the local guard, and
   derive `NoLateRegistration s -> SafeStep e s t ->
   NoLateRegistration t`, followed by the explicit `SupportOrder` result;
6. instantiate the existing `SupportTraceContract` and derive endpoint
   SupportWF/well-foundedness for safe reached traces;
7. define total provision only for successful completed activations (D69),
   and use T04 `ActivationProvenance` to prove that every active fiber at a
   reached, quiescent, nonfailed endpoint comes either from a recorded
   successful finish or a valid initial commit certificate, with committed
   keys equal to declared provisions;
8. prove that reached + WellFormed + safe support profile + quiescent +
   nonfailed + total provision + parent-retirement closure imply
   `SupportOperator snapshot active = active`, then use P11's
   `supportSet_eq_active` hook to conclude L70.

The required negative trace must realize the accepted three-edge cycle, not
merely an arbitrary cyclic snapshot:

~~~text
n -> r     precedence/provider edge
r -> c     parent edge: parent(c) = r
c -> n     parent edge: parent(n) = c
~~~

Use the accepted ADR-09 labels (`r = 0`, `c = 1`, `n = 2`) or record an
explicit bijection to them. A concrete trace must start from an
`Initial /\ WellFormed` source, include the retired/reloading child, former
provider removal, and late registration required by H04, and end in the
corrected projection above. T59 must establish endpoint WellFormedness;
lifetime freshness must hold; the precedence fragment must remain acyclic;
the combined projection must prove `not SupportWF`.

If any step is not reachable under T03's actual guards, stop and report the
exact mismatch. The safe profile itself may not mention endpoint
`SupportOrder`, `SupportWF`, `CommittedSnapshot`, or a preservation field. Do
not change `SupportRel` direction, hide the order inside WellFormed, assume the
active fixed-point equation in L70, or label an abstract graph fixture semantic
evidence.

Also provide negative evidence showing that L70 fails without total provision
and need not hold at a nonquiescent endpoint.

## 16. `P13-T05D` — spatial ordering and progress

Complete the old-paper single-realm T63 and the repaired T66:

* prove both halves of T63 from actual rule guards and structural facts:
  provider activation precedes consumer activation, and consumer withdrawal
  precedes provider withdrawal; the latter consumes `R.withdraw`, D50, and the
  relied/provider trace guards;
* define a global lifecycle measure using finite live incarnations, lifecycle
  phase, iterator rank, pending landing/cleanup work, and the immutable
  precedence/allocation data;
* prove lifecycle successors decrease the appropriate measure or inhabit a
  well-founded lifecycle relation;
* prove `LifecycleReady` from the relevant reached/WF profile and preserve it
  across lifecycle steps using the T02 begin/iter/finish/cleanup existence and
  landing-or-abort totality laws;
* prove the progress disjunction for an arbitrary suitably reached state:
  it is quiescent/terminal or has a lifecycle successor;
* derive the ADR-05 uniform per-incarnation bound, a bound for every arbitrary
  lifecycle-only trace from the reached source, a finite global bound,
  well-founded lifecycle termination, and endpoint quiescence for a maximal
  trace, where maximal means that the endpoint has no lifecycle successor
  (T66).

The theorem concerns a lifecycle-only suffix after an orchestration prefix.
It must not assume that the whole trace from an empty registry is
lifecycle-only, introduce a runtime scheduler, depend on fairness, or assume
termination/rank-certificate conclusions in its premises. Empty systems remain
covered by the theorem, but nonvacuity is established by T08 fixtures rather
than by adding artificial nonempty premises to every theorem.

Scoped resolution is not part of T63. A realm-aware provider-order theorem is
post-P13 work.

## 17. `P13-T05E` — full alpha transport and adjacent transposition

Finish L56 and prove L71:

* transport GlobalState, ordered name history, labels, coded payloads, rule
  witnesses, traces, reached states, episodes, WF, quiescence, support
  projection, and relevant equivalences under a permutation of incarnation
  names;
* keep provision keys and the single-realm coeffect carrier fixed unless a
  separate accepted profile says otherwise;
* prove identity, composition, inverse/cancellation, and a nonidentity finite
  swap;
* prove the two paper-promised local diamonds: distinct-fiber
  activation/activation and compatible activation/orchestration;
* expose disjoint footprints, same-witness replay, continuation stability,
  absence of registration/name conflicts, and compatible control edits in the
  L71 premises.

Local map commutation or P12 store frame laws alone are insufficient for a
labelled-step diamond. The result must construct the swapped actual steps and
relate their endpoints with the correct D53 equivalence.

## 18. `P13-T06` — closed-episode deletion

Prove the repaired L72 only after T05A/B/C have joined. Its statement must
name, rather than hide:

* the containing trace's reachability and WellFormedness;
* the selected closed episode and its actor;
* C62 recovery and all required operation/continuation independence;
* absence or controlled treatment of registered-child/dependent episodes;
* total provision, relied/provider restrictions, and the complete L70
  quiescence/nonfailure/support-order envelope;
* the structural/vestigial deletion conditions from L54/L57/T59.

Construct the shortened trace, prove its label/input effect, endpoint
observation, WF, name-ledger, provider, and support properties, and show that it
uses the authoritative rules. A theorem that simply assumes the shortened
trace exists is only a contract and does not complete L72.

## 19. `P13-T07` — canonical form, confluence, and unique normal form

Complete T73 as three separately named results:

1. **canonicalization:** for reachable/WF traces with finite episode/support
   domain, corrected SupportOrder, total provision, quiescent nonfailed
   endpoints, the T02 semantic determinism/coherence profile (or identical
   resolved witnesses), pairwise independence/continuation stability, and the
   exact L70/L71/L72 applicability envelope, normalize an admissible trace with
   the stated completed-episode premises into support-compatible episode order,
   modulo alpha and the exact D53 equivalences;
2. **quiescent endpoint confluence:** two admissible, nonfailed traces with the
   complete canonicalization envelope from item 1 and T04
   `SameOrderedOrchestrationInputs` have related quiescent endpoints. They use
   either the T02 semantic confluence profile or a separately stated
   `SameResolvedSemanticWitnesses` premise. The conclusion carries an explicit
   nonidentity-capable permutation witness and separately stated D33-state and
   D53-episode conclusions, in the form
   `exists chi, StateObs ... /\ EpisodeEq ...` (up to repository
   naming/orientation), rather than hiding alpha in an opaque relation;
3. **unique-normal-form corollary:** inherit the complete item-2 envelope and
   add T66 termination/maximality to obtain uniqueness of normal endpoints.

The full H04 T73 row requires the confluence-profile theorem under the same
external orchestration inputs. A theorem that additionally assumes identical
resolved internal witnesses is a useful restricted result but cannot, by
itself, complete T73; record that strengthening in the Ledger if it is the only
version delivered.

Here admissibility/episode completion does not imply `nonfailed`. Do not define
an ambiguous `SuccessfulTrace` that makes the separate nofailure premise
redundant; the negative failure fixture must be able to satisfy every premise
except nofailure.

Do not replace "same ordered orchestration inputs" with "same final
configuration", and do not make endpoint confluence depend circularly on the
unique-normal-form corollary. Failure and overlapping effects remain excluded
unless their extra compatibility hypotheses are proved.

Include negative finite evidence isolating why nofailure and independence are
necessary: the failure fixture satisfies every other T73 premise, and the
overlapping-effect fixture satisfies every other premise including nofailure,
yet their schedules reach inequivalent endpoints.

## 20. `P13-T08` — finite vertical slice and P13 conformance manifest

Create one nontrivial finite vertical slice that exercises the production
state and actual rules. Across the fixture family, require all of:

* a nonempty WellFormed initial state and a nonempty full-rule trace;
* every printed rule case, every concrete constructor, and both Divert branches
  used by one trace or separately inhabited by real rule witnesses;
* at least two acting fibers;
* a nonempty requirement/provision and one completed activation;
* nested registration;
* async diversion and a real failure/raise/cleanup path;
* a nonidentity name permutation;
* two syntactically distinct schedules related by T04
  `SameOrderedOrchestrationInputs`, including its growing name bijection;
* concrete activation and withdrawal traces exercising both halves of T63;
* a safe `SupportOrder` endpoint and the reachable cyclic `not SupportWF`
  endpoint, with the latter reached from an initial WellFormed source and
  retaining endpoint WF, lifetime freshness, and acyclic precedence;
* separate related and unrelated witnesses for the D33 and D53 relations,
  including evidence that neither is silently interchangeable with the other;
* positive canonical/confluence evidence and the required negative profiles.

Use theorem/example blocks and `by decide` where appropriate; do not add
top-level `#eval` over exposed library declarations. Finite evaluation is `E`,
not a replacement for general `K` proofs.

Add `STC/Conformance/Global.lean` as a checked theorem/declaration inventory.
T08 defines and tests `scripts/generate_p13_conformance_manifest.py` and its
schema. The final `docs/status/P13-conformance-manifest.json` is generated by
T09 only after the final Ledger, Blueprint, Bootstrap, and guidance edits.
It records source hashes, declaration names, evidence dimensions,
repaired-paper mapping, exact assumptions, finite fixture outcomes, row
states, and explicit R0/R1+ boundaries.

The generator CLI contract is:

~~~text
python scripts/generate_p13_conformance_manifest.py \
  --output docs/status/P13-conformance-manifest.json
python scripts/generate_p13_conformance_manifest.py \
  --check --output docs/status/P13-conformance-manifest.json
~~~

Write mode may create or replace only the named P13 output. `--check` is
non-mutating and fails on any byte/content drift. Both modes reject the P8
manifest path, output is deterministic for a fixed tree, and no implicit
timestamp may make repeat runs differ. T08 may use an untracked temporary
output to test these properties; it does not commit a pre-T09 manifest.

P12 appears in this manifest as a completed independent typed-scoping layer.
The manifest must explicitly say that no realm-aware global Section-4 theorem
or arbitrary flattening converse was proved.

## 21. `P13-T09` — cumulative integration and Definition Ledger

The central integration owner performs this task after every lane is green.

### 21.1 Bootstrap and live guidance

Update Bootstrap so the full build reaches all new production modules,
conformance declarations, and finite examples. Keep imports sorted and update
the module docstring/declaration inventory. `STC.lean` should normally remain a
single Bootstrap import.

Reconcile live README, AGENTS, and Blueprint Markdown/JSON so they say:

* P9 through P12 are complete on the recorded ancestry;
* P13's actual task/gate state and concrete module graph;
* old-paper single-realm global metatheory is complete only if every P13 gate
  passed;
* Scoped global generalization, newer-paper reconciliation, and Cordis R1+
  remain separate work.

Do not rewrite dated snapshots or accepted architecture records.

### 21.2 Ledger protocol

Edit `docs/status/Definition-Ledger.json` in place. Never run
`gen_definition_ledger.py`. Preserve all 82 IDs and every frozen ID, title,
kind, anchor, `depends_on`, treatment, H04 target/relation/blocker/readiness,
and source hash field.

Use exactly:

~~~text
delivery: planned | in_progress | completed | blocked | deferred
evidence: pending | aligned | passed | proved | tested | seam_only | deferred | not_applicable
~~~

Dependency-open work uses `planned`/`in_progress` with an exact
`deferred_reason`. Reserve delivery `deferred` for deliberately excluded,
refinement-only, or not-yet-derived SUBSUMED rows. This preserves the normalized
post-P12 convention and avoids mixing two meanings of deferred.

Each promoted row must name its checked declaration(s), actual target module,
evidence dimension, theorem strength, all repaired premises, and any remaining
gap. A row becomes `completed/proved` only when its full H04 production target
is derived. Definitions with executable data but no claimed law may use
`completed/tested`; a structure field alone cannot justify `proved`.

Expected adjudication, conditional on all corresponding gates passing:

| Task | Rows eligible for completion |
|---|---|
| T01A | D17, L18, T20, C21 |
| T01B | D22, D23, D24, D25, SAT |
| T01C | L38 |
| T02 instance gate | D32, D33 |
| T02/T03 | D43--D50, D58, R.base, R.withdraw, R.iter, A.async, R.fail, R.full |
| T04 | D53 |
| T05A | L54, L55, L57, T59, Table1 |
| T05B | D60, T61, C62, T64 |
| T05C | D65, D67, L68, D69, L70 |
| T05D | T63, T66 |
| T05E | L56, L71 |
| T06 | L72 |
| T07 | T73 |

For L68, `completed/proved` means the H04-repaired theorem plus the required
reachable counterexample; it does not revive the rejected literal claim. For
T66, it means the repaired reachable-suffix theorem plus nonvacuity evidence,
not a separate negative theorem.
For Table1, completion means a checked, derived per-constructor inventory while
the frozen `SUBSUMED` treatment remains unchanged. If a theorem still assumes
its desired concrete guard preservation, active fixed point, shortened trace,
or confluence conclusion, retain `in_progress` and state the exact missing
implication.

D27 and D74 remain deferred under their frozen H04 dispositions. D26,
D34/L35, D39/T40, and D41/T42 remain explicit non-P13 backlog unless separately
authorized and proved; do not alter them merely to make the final counts look
complete.

Append row-specific accepted-architecture provenance only where the checked
declarations justify it: ADR-07 for concrete Control/rule/trace results,
ADR-08 for Staging/base-view results, and ADR-09 for support results. Do not add
ADR-10 to single-realm theorems merely because P12 is merged. Preserve existing
`adr_refs` and every frozen H03/H04 field.

Here “delivery” and “evidence” refer to the existing JSON fields
`delivery_status` and `evidence_state`; do not add parallel shorthand keys.

After all T09 source/document/Ledger edits, generate the final manifest in
write mode, validate its JSON, and immediately run non-mutating `--check`.

## 22. Required validation

Every touched Lean file must pass its own repository-flag check with zero
errors and zero linter warnings:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true <touched-file>
~~~

Run narrow checks after each task, full builds at both API freezes and every
join, and the final suite:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build

python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
jq -e . docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
python scripts/generate_p13_conformance_manifest.py \
  --output docs/status/P13-conformance-manifest.json
jq -e . docs/status/P13-conformance-manifest.json
python scripts/generate_p13_conformance_manifest.py \
  --check --output docs/status/P13-conformance-manifest.json

P13_SCAN_EXIT=0
python scripts/scan_lean.py STC > /tmp/p13-scan-output.txt 2>&1 || \
  P13_SCAN_EXIT=$?
{
  printf 'command: python scripts/scan_lean.py STC\n'
  printf 'exit: %s\n' "$P13_SCAN_EXIT"
  if test "$P13_SCAN_EXIT" -eq 1; then
    printf 'classification: clean/no matches\n'
  elif test "$P13_SCAN_EXIT" -eq 0; then
    printf 'classification: lexical matches require review below\n'
  else
    printf 'classification: scanner failure\n'
  fi
  sed -n '1,240p' /tmp/p13-scan-output.txt
} > docs/status/P13-scan-raw.txt
test "$P13_SCAN_EXIT" -eq 0 -o "$P13_SCAN_EXIT" -eq 1

git diff --check

P13_IMPORT_EXIT=0
rg -n '^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+STC\.(Examples|Conformance)|architecture-decision/lean-spike|STCADR0[0-9]+' \
  STC/Core/Effect STC/Core/Partial STC/Core/Coeffect.lean \
  STC/Foundation/Relation/Transport.lean STC/State/Positive.lean \
  STC/State/Observation/Lift.lean STC/State/Component.lean \
  STC/State/Fiber.lean STC/State/Global.lean STC/State/Global \
  STC/Control/Rules.lean STC/Control/Reachability.lean \
  STC/Control/Structural.lean STC/Control/Preservation.lean \
  STC/Control/Recovery.lean STC/Control/Spatial.lean \
  STC/Control/Progress.lean STC/Control/Support \
  STC/Control/Alpha.lean STC/Control/Commutation.lean \
  STC/Control/Episode.lean STC/Control/Deletion.lean \
  STC/Control/Canonical.lean > /tmp/p13-import-boundary.txt 2>&1 || \
  P13_IMPORT_EXIT=$?
sed -n '1,240p' /tmp/p13-import-boundary.txt
test "$P13_IMPORT_EXIT" -eq 1

P13_FORBIDDEN_EXIT=0
rg -n 'sorry|admit|axiom|unsafe' \
  STC/Core/Effect STC/Core/Partial STC/Core/Coeffect.lean \
  STC/Foundation/Relation STC/State/Component.lean STC/State/Fiber.lean \
  STC/State/Global.lean STC/State/Observation STC/Control \
  STC/Conformance/Global.lean STC/Examples/Global.lean \
  STC/Examples/SupportCycle.lean > /tmp/p13-forbidden.txt 2>&1 || \
  P13_FORBIDDEN_EXIT=$?
sed -n '1,240p' /tmp/p13-forbidden.txt
test "$P13_FORBIDDEN_EXIT" -eq 1
~~~

The scanner raw record is written before its status is adjudicated. Scanner
exit 1 is clean; exit 0 requires line-by-line classification appended to that
record (and preferably a clean rerun after removable false positives); exit 2
is failure. Production imports of examples/conformance or historical spikes
are a hard failure. The two targeted negative `rg` scans preserve their output
before the assertion and must end at exit 1; exit 0 means matches that must be
removed or resolved through a recorded reopen, and exit 2 is an error.

Against the recorded execution base, require clean protected diffs:

~~~bash
git diff --exit-code <p13-base> -- STC/Control.lean
git diff --exit-code <p13-base> -- STC/Control/Support.lean
git diff --exit-code <p13-base> -- STC/Staging.lean
git diff --exit-code <p13-base> -- STC/Staging/Support.lean
git diff --exit-code <p13-base> -- STC/State/Support.lean
git diff --exit-code <p13-base> -- STC/State/Support/Closure.lean
git diff --exit-code <p13-base> -- STC/State/Support/Alpha.lean
git diff --exit-code <p13-base> -- STC/Alpha
git diff --exit-code <p13-base> -- STC/Scoped.lean STC/Scoped
git diff --exit-code <p13-base> -- STC/Conformance/Manifest.lean
git diff --exit-code <p13-base> -- STC.lean
git diff --exit-code <p13-base> -- \
  STC/Core/Effect.lean STC/Core/Partial.lean STC/Core/Iterator.lean \
  STC/Foundation/Relation.lean STC/State/CoeffectStore.lean \
  STC/State/Like.lean STC/State/Observation.lean \
  STC/State/RegistryLike.lean STC/State/FinmapAdapter.lean
git diff --exit-code <p13-base> -- \
  STC/Examples/Control.lean STC/Examples/Staging.lean \
  STC/Examples/Support.lean STC/Examples/SupportTrace.lean \
  STC/Examples/Scoped.lean
git diff --exit-code <p13-base> -- docs/status/P8-conformance-manifest.json
git diff --exit-code <p13-base> -- docs/blueprint/baseline
git diff --exit-code <p13-base> -- docs/blueprint/architecture-decision
git diff --name-only <p13-base>
git status --short --branch
~~~

If a protected-path change was separately approved after a stop/reopen, replace
the corresponding clean-diff gate with the recorded approval and a focused API
compatibility proof; never silently omit it.

## 23. Acceptance criteria

P13 is phase-complete only when all of the following hold:

1. the execution base contains P11, P12, and this plan, and a fresh integrated
   baseline build passes;
2. all twelve transitive prerequisites have checked downstream-usable
   declarations;
3. the state carrier is positive/data-only, retains lifetime freshness and
   ordered birth data, exposes no hidden support certificate, and freezes
   alpha, replay/factorization, progress-existence, and semantic-coherence
   profiles;
4. one concrete guarded calculus covers every printed 3+7 case, with explicit
   mapping for any constructor split, derived subfamily/Staging views, and
   inhabited rule witnesses;
5. reachability, episodes, factorization, and all distinct observational
   relations are explicit and frozen; external orchestration-input equality is
   separate from internal resolved-witness equality, and initial/reached active
   fibers carry preserved activation provenance;
6. structural facts are derived by rule cases, and WellFormed preservation is
   proved rather than assumed in successors;
7. ranked iterator semantics is connected to the successful-stage/Reach
   relation and uniform bounds; a transformation monoid is claimed only for
   its total deterministic nonfailing specialization; T61/C62/T64 expose
   recovery and independence assumptions exactly;
8. the real L68 cycle is reached from an initial WellFormed source under the
   unrestricted rules with endpoint WF/freshness and acyclic precedence, while
   the noncircular named safe profile rejects its first bad step and yields
   concrete trace support-order preservation;
9. L70 derives its active fixed-point premise from reachable semantic
   conditions and valid finish/initial-commit activation provenance;
10. both activation and withdrawal halves of T63 are explicitly single-realm,
    and T66 uses the structural readiness/existence profile plus ADR-05 uniform
    bounds to prove nonvacuous progress, arbitrary-suffix bounds, maximal-run
    lifecycle termination, and quiescence without a scheduler or fairness;
11. full alpha transport has a nonidentity witness, and L71 constructs real
    swapped steps for its promised cases;
12. L72 constructs a valid shortened trace under its complete envelope;
13. T73 uses the precise growing-bijection orchestration-input relation and
    semantic coherence/same-witness envelope; canonicalization and endpoint
    confluence are separate from the termination-dependent unique-normal-form
    corollary;
14. finite evidence meets every T08 nonvacuity and negative-evidence gate;
15. the new deterministic P13 manifest is checked and the P8 manifest is
    unchanged;
16. Bootstrap, live guidance, and the Ledger describe exactly the evidence
    delivered, with no architecture/runtime overclaim;
17. focused Lean checks, API-freeze builds, final build, Ledger validation,
    scanner classification, manifest check, and diff gates all pass;
18. the final handoff records actual commits, declarations, assumptions,
    counterexamples, row deltas, commands, exit codes, and residual work.

## 24. Stop and reopen rules

Stop rather than improvise if:

* the fresh integrated build cannot run or fails;
* a registry cell would need to contain `RawState -> RawState`,
  `RawState -> Prop`, a state-indexed iterator closure, or an equivalent
  negative recursive occurrence;
* any name-bearing code cannot be classified as name-neutral or given an
  alpha action plus interpreter-equivariance law at the T02 freeze;
* D53 factorization works only through a constant-after-state map or another
  nonreplayable witness;
* the proof needs to change an accepted state carrier, `SupportRel` direction,
  the positive support LFP, lifetime freshness, or an accepted ADR boundary;
* the concrete calculus needs a scheduler/fairness axiom, a second mutable
  global store, hidden runtime behavior, or an arbitrary scoped-to-flat
  projection;
* a lifecycle rule allocates/registers a name rather than using an explicit
  orchestration insertion, so the T66 finite-live suffix measure is not closed;
* D60/T61/T64 can be obtained only by choosing a nondeterministic success
  branch or totalizing failure to manufacture a transformation monoid;
* progress can be obtained only by defining `LifecycleReady` as successor
  existence, assuming stage/cleanup/landing totality after the fact, or adding
  scheduler/fairness;
* T73 lacks successful-result/continuation/landing coherence and its input
  relation does not retain the same resolved witnesses;
* L70 needs to treat a pre-populated active initial fiber but no valid initial
  commit certificate or preserved `ActivationProvenance` is available;
* the accepted L68 cycle cannot be reached under the concrete guards;
* safe L68 can be proved only by silently strengthening authoritative
  `R.full`, or by mentioning endpoint `SupportOrder`/`SupportWF` inside its
  local guard, instead of defining a named restricted profile;
* T59 works only by assuming successor WellFormedness, T66 only by assuming
  termination/rank conclusions, or L70 only by assuming its active fixed
  point;
* L71 lacks same-witness replay/continuation stability, L72 assumes the
  shortened trace, or T73 lacks full alpha, the precise growing-bijection
  input relation, semantic coherence, L71, L72, or T66 where required;
* a protected merged API must change;
* finite computation is the only support for a row proposed as `proved`.

The reopen report must identify the smallest conflicting signature, rule,
guard, or theorem and classify it as source defect, accepted-ADR conflict,
Lean engineering, or scope change. Semantic changes require a superseding ADR
or explicit lead decision, not a lane-local workaround.

## 25. Handoff and post-P13 boundary

Create `docs/status/P13-handoff-report.md` with:

* plan/task IDs and per-task result;
* branch, actual base/head, required ancestors, checkpoint commits, and clean
  tree state;
* final module/import DAG and protected-path confirmation;
* T02/T03/T04 freeze commits, signature inventories, module hashes, and proof
  that no post-freeze signature changed (or the exact coordinated reopen);
* every lane's base/head, merge order, changed-path allowlist result, and lane
  record;
* public declaration and theorem inventory;
* exact premises and repaired-paper correspondence of every K result;
* the reachable support-cycle trace and all other negative/nonvacuity evidence;
* A/I/K/E/R0/R1+ classification;
* itemized Ledger before/after values and residual rows;
* Blueprint/manifest JSON validation and the final manifest hash/check result,
  including confirmation it was regenerated after the last Ledger/Blueprint
  edit;
* exact commands, exit codes, build job count, scanner raw output and
  classification;
* the Ledger validator's 82/82 result and both frozen H03/H04 hash results;
* failed approaches, reopen decisions, and unresolved blockers.

Successful P13 closes the intended old-paper, single-realm Section-4
production/metatheory phase. It does **not** mean the entire research program
is finished. The explicit post-P13 boundary is:

* D27 expository realization and D74 declarative/runtime refinement under
  their frozen H04 dispositions;
* Cordis R1+ refinement;
* D26, D34/L35, D39/T40, and D41/T42 unless separately scheduled;
* realm-aware global Control/Support/T63/L70/T73 generalization over P12;
* deep `EffectCode` or other runtime engineering not required by the repaired
  Section-4 theorems;
* reconciliation with newer arXiv paper versions and their rationale.

Those are later explicit phases. They must not be smuggled into P13 or used to
weaken its old-plan acceptance gates.
