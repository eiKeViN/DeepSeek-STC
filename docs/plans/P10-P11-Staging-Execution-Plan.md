# STC P10 Control and P11 Staging Execution Plan

| Field | Value |
|---|---|
| Plan ID | DH-P10-P11-STAGING-EXEC-01 |
| Repository | https://github.com/eiKeViN/DeepSeek-STC |
| Prepared | 2026-08-29 |
| Planning baseline | origin/main at 2f83afb, post-P9 merge |
| Depends on | P8 complete; P9 complete; ADR-07 and ADR-08 accepted |
| Scope | production Control interfaces and evidence, followed by the derived base/full Staging view |
| Ownership | one agent, sequentially: P10 must freeze its API before P11 Staging begins |
| Namespace | STC.Control and STC.Staging |
| Status | ready to schedule from the common post-planning merge |

This lane implements the accepted ADR-07 control architecture and then consumes
that exact production API to implement the accepted ADR-08 staging architecture.
It is deliberately a single sequential lane: the Staging owner must not guess a
Control relation, Step, or Trace API while Control is still changing.

The lane does not implement support well-foundedness, scoped coeffects, the
global Section-4 theorem cluster, or a Cordis runtime. It may establish local
interface and kernel evidence, but it must not convert production compilation
into a claim of global preservation, progress, confluence, or R1+ refinement.

## 1. Authority and accepted-decision baseline

The paper remains authoritative for literal source claims. Frozen H03/H04 and
the Formal Reference preserve audited provenance and defects. The repaired
formal target for this lane is governed by accepted ADR-01 through ADR-08,
including the independent P9 acceptance records:

~~~text
docs/blueprint/architecture-decision/status/ADR-07-accepted.json
docs/blueprint/architecture-decision/status/ADR-08-accepted.json
~~~

Those records report record_status = accepted, architecture_status = closed,
and formal_acceptance = true. Candidate ADR Markdown/JSON files and historical
Lean spikes retain their earlier proposed metadata as frozen provenance. P8's
manifest is likewise a historical pre-P9 snapshot. Neither fact reopens P9.

When older Blueprint, AGENTS, README, candidate-packet, or P8 prose still says
proposed or acceptance_pending, the later P9 acceptance records and
docs/status/P9-handoff-report.md govern the current architecture status. The
lane must record this snapshot distinction and must not rewrite historical
candidate bytes to make the wording uniform.

The accepted boundaries are:

* ADR-07: orchestration and lifecycle are distinct relation classes; typed
  Step witnesses retain their class and rule label; the abstract semantics
  contains no scheduler; InFlight, landing/abort, complete failure payload,
  and freshness metadata boundaries remain explicit.
* ADR-08: R+ is the sole authoritative transition semantics; Rb is an
  AtomicProfile-controlled finite macro/view with embedding, projection,
  stable-image, forward-simulation, and profile-relative adequacy contracts.
  Rb is never a second independently maintained calculus.

Evidence dimensions remain separate:

* A: source/ADR alignment;
* I: interface elaboration and build evidence;
* K: substantive checked theorem;
* E: finite executable evidence;
* R0: abstract adapter seam;
* R1+: concrete runtime refinement.

This lane targets A/I/K/E only. It produces no R1+ evidence.

## 2. Entry gate and reproducible preflight

Create the execution branch from the commit containing this plan after all
three parallel plans have merged. The branch must include P9 commit c6f1a3a
and merge commit 2f83afb.

~~~bash
git fetch origin --prune
git switch -c <control-staging-branch> origin/main
git status --short --branch
git log -1 --oneline
git merge-base --is-ancestor 2f83afb HEAD
~~~

The final command must exit 0. Record the actual branch base in the P10
handoff rather than copying the planning baseline mechanically.

Read without modifying:

~~~text
AGENTS.md
README.md
lean-toolchain
lakefile.toml
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
STC/Alpha/Core.lean
STC/Alpha/Trace.lean
STC/Alpha/Transport.lean
STC/Examples/TwoCounter.lean
STC/Examples/VerticalSlice.lean
STC/Conformance/Manifest.lean
docs/status/P7-handoff-report.md
docs/status/P8-handoff-report.md
docs/status/P8-conformance-manifest.json
docs/status/P9-handoff-report.md
docs/status/Definition-Ledger.json
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.md
docs/blueprint/DeepSeek-Harness-11-Executable-Formalization-Blueprint.json
docs/blueprint/architecture-decision/md/DeepSeek-Harness-12-ADR-07-Control-Architecture.md
docs/blueprint/architecture-decision/json/DeepSeek-Harness-12-ADR-07-Control-Architecture.json
docs/blueprint/architecture-decision/status/ADR-07-accepted.json
docs/blueprint/architecture-decision/md/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture.md
docs/blueprint/architecture-decision/json/DeepSeek-Harness-13-ADR-08-Base-Extended-Staging-Architecture.json
docs/blueprint/architecture-decision/status/ADR-08-accepted.json
~~~

The Lean spikes are read-only architecture mirrors. They may be consulted, but
production files must not import them and must not duplicate their local
STCADR07/STCADR08 result, trace, or toy namespaces.

Run and record:

~~~bash
jq -e '.record_status == "accepted" and
       .architecture_status == "closed" and
       .formal_acceptance == true' \
  docs/blueprint/architecture-decision/status/ADR-07-accepted.json
jq -e '.record_status == "accepted" and
       .architecture_status == "closed" and
       .formal_acceptance == true' \
  docs/blueprint/architecture-decision/status/ADR-08-accepted.json
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/generate_conformance_manifest.py
python scripts/scan_lean.py STC
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Bootstrap.lean
lake build
~~~

The scanner contract is exit 1 = clean, exit 0 = lexical match requiring
classification, and exit 2 = scanner failure. A failed acceptance check,
ledger validation, build, or source-integrity check blocks this lane.

## 3. Ownership and parallel-work boundary

This lane owns:

~~~text
STC/Control.lean
STC/Control/**
STC/Staging.lean
STC/Staging/**
STC/Examples/Control.lean
STC/Examples/Staging.lean
docs/status/P10-api-freeze.md
docs/status/P10-handoff-report.md
docs/status/P10-scan-raw.txt
docs/status/P11-staging-handoff-report.md
docs/status/P11-staging-scan-raw.txt
~~~

It must not edit:

~~~text
STC/State/Support.lean
STC/Examples/Support.lean
STC/Scoped.lean
STC/Scoped/**
STC/Examples/Scoped.lean
STC.lean
STC/Bootstrap.lean
docs/status/Definition-Ledger.json
docs/status/P8-conformance-manifest.json
docs/blueprint/**
AGENTS.md
README.md
~~~

The last seven paths are integration-owned or frozen/current-guidance inputs.
This lane reports proposed ledger/status changes in its handoffs; the
integration owner applies them after merging all parallel lanes.

No Control or Staging theorem may depend on files from the Support or Scoped
parallel branches. The only permitted common dependencies are files already
present at the common branch base.

## 4. Dependency order and checkpoints

The required sequence is:

~~~text
P10-PREP
  -> P10-T01 control state and in-flight boundary
  -> P10-T02 labels, relation classes, and typed steps
  -> P10-T03 indexed traces and admissibility policy
  -> P10-T04 async, failure, and freshness boundaries
  -> P10-T05 nonvacuous finite control evidence
  -> P10-GATE/API-FREEZE
  -> P11S-T01 staging model over frozen Control
  -> P11S-T02 atomic macro/view and derived Rb
  -> P11S-T03 forward simulation and trace composition
  -> P11S-T04 profile-relative adequacy and stable image
  -> P11S-T05 finite positive and negative evidence
  -> P11-STAGING-GATE
~~~

P11S-T01 must consume the exact P10 Control API. Once P10-GATE is recorded,
Staging may not edit Control files. If the Staging work exposes a genuine
Control-interface defect, stop, record the issue and affected declarations,
and reopen P10 through an explicit integration decision rather than patching
Control opportunistically.

## 5. P10-T01 — control state and in-flight boundary

Create a production carrier layer under STC/Control. The suggested file split
is:

~~~text
STC/Control/State.lean
STC/Control/Label.lean
STC/Control/Step.lean
STC/Control/Trace.lean
STC/Control/Async.lean
STC/Control/Failure.lean
STC/Control.lean
~~~

The split may be adjusted only if the import DAG remains acyclic and each
declaration has a single production source.

Port the accepted shapes, parameterized over the existing state interfaces:

* ControlMode with inactive, reloading, active, and unloading modes;
* LandingChoice with explicit abort/land cases;
* LandingWitness tying a future/token to an admissibility predicate;
* InFlight containing owner/incarnation, launch snapshot, committed view,
  remaining continuation, successful-prefix accumulator, and the mandatory
  landing witness;
* ControlState containing raw state, metadata, mode, optional InFlight, and
  optional outcome.

Do not:

* store an unrestricted scheduler or promise implementation;
* recompute the committed view or selected landing witness at landing time;
* place a recursive state transformer into a registry cell;
* hide ledger/freshness history inside the default core observation;
* duplicate STC.EffectResult, STC.Failure, STC.ExecResult, RankedIterator,
  NameLedger, NameTrace, or AlphaBoundary.

Use the existing Foundation.Result, Core.Iterator, State, and Alpha contracts.
If an accumulator is specialized to a function, its relation/properness law
must remain explicit.

## 6. P10-T02 — relation classes, labels, and typed Step

Define separate orchestration and lifecycle label families retaining the
accepted payload boundaries:

~~~text
O-Insert  fresh incarnation plus component payload
O-Retire  target incarnation
O-Remove  target incarnation

L-Begin   incarnation plus committed target view
L-Iter    incarnation plus selected continuation
L-Finish  incarnation
L-Divert  incarnation plus abort/land choice
L-Raise   incarnation plus complete Failure payload
L-Leave   incarnation
L-Unload  incarnation
~~~

The production model must expose two distinct relations:

~~~text
orchestration : OrchestrationLabel -> State -> State -> Prop
lifecycle     : LifecycleLabel     -> State -> State -> Prop
~~~

Define a small ControlModel or equivalent explicit record that packages these
relations without a scheduler. Define indexed, witness-carrying Step
constructors whose before/after states and relation premise prevent:

* using an orchestration premise as a lifecycle premise;
* erasing the rule label;
* treating failure as Option.none or identity;
* inventing an unlabelled union as the authoritative source.

If an erased step relation is useful for generic lemmas, derive it from typed
Step and keep the erasure theorem explicit. It must not replace the typed API.

## 7. P10-T03 — trace, admissibility, and lifecycle suffix

Define one authoritative finite indexed Trace over typed Control steps.
Staging will reuse this type; do not create a second production trace carrier.

Required operations and laws:

* empty/single/cons or equivalent indexed constructors;
* labels and length;
* append with endpoint indexing and length/label laws;
* classification of an all-lifecycle trace;
* HasLifecycleSuccessor;
* MaximalLifecycleSuffix;
* TracePolicy with initial-state, label/class filter, and per-step hook;
* stepsOk and admissible;
* a lifecycle-only policy specialization.

Required checked evidence includes:

* a trace containing an orchestration step is not lifecycle-only;
* a lifecycle suffix can satisfy the policy independently of the preceding
  external input;
* the finite append theorem used later by Staging is nonvacuous;
* maximality states the absence of a lifecycle successor at the endpoint,
  not the absence of all orchestration inputs.

Do not claim global progress, existence of a maximal suffix for every reachable
state, or termination of the full lifecycle relation in P10. Those require the
later theorem envelope and explicit rank/reachability premises.

## 8. P10-T04 — asynchrony, failure, and freshness

### 8.1 Asynchrony

Define AsyncPolicy or an equivalent explicit law record with:

* permitted landing/abort choices;
* a link to the InFlight landing witness;
* an explicit iterator/stage boundary for abort;
* no scheduler or fairness field.

Prove that landing allowed by the policy retains the relevant witness. Add a
negative finite case forbidding a mid-stage abort or unrelated landing.

### 8.2 Failure

Use STC.Failure and STC.ExecResult. The L-Raise constructor/label must retain:

* error;
* boundary state;
* successful-prefix undo.

Provide small bridge lemmas showing that the label preserves the complete
failure payload and cannot be manufactured from a success result. Do not
redefine the P3/P4 failure carrier.

### 8.3 Freshness

Connect the orchestration boundary to P6 NameLedger/AlphaBoundary interfaces.
The control layer may expose metadata ports for current freshness, historical
no-reuse, parent references, and name-aware traces. It must not:

* replace incarnation identity by raw Nat reuse;
* claim name-bearing continuation/control-payload equivariance without a
  corresponding action and theorem;
* make the default core observer inspect allocation history.

Any alpha theorem delivered here must use a non-identity finite permutation
and a name-bearing field.

## 9. P10-T05 — finite control fixture and gate

Create STC/Examples/Control.lean with a finite model that has:

* at least one orchestration step;
* at least two lifecycle steps;
* an explicit reloading/active or unloading/terminal path;
* a finite typed trace with a proved positive length;
* a lifecycle-only suffix and a maximal terminal suffix;
* one allowed landing and one rejected abort/landing case;
* one complete failure payload check;
* one freshness/name-bearing boundary check where applicable.

The relations must be inhabited by meaningful states. Empty relations,
impossible initial predicates, and behavior-erasing observations are forbidden.

At P10-GATE run focused checks for every new file, then:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Control.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Control.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
git diff --check
~~~

Write docs/status/P10-api-freeze.md containing:

* exact branch/base and commit;
* public module/declaration inventory;
* accepted ADR-07 record hash;
* focused command outputs;
* exact theorem evidence;
* deferred Control obligations;
* an explicit statement that Staging may consume but not modify this API.

P10 is not complete until this freeze record exists and all checks pass.

## 10. P11S-T01 — staging model over frozen Control

Implement the accepted ADR-08 production surface under STC/Staging only after
P10-GATE. Suggested split:

~~~text
STC/Staging/Model.lean
STC/Staging/Macro.lean
STC/Staging/Simulation.lean
STC/Staging.lean
~~~

The model must consume:

* the frozen Control orchestration/lifecycle relations;
* the frozen typed Step/Trace API;
* base and extended states;
* embed, project, and stable-image data;
* base labels and their finite full-label expansions;
* explicit atomicity/profile premises.

The full R+ semantics is the Control relation. Staging must not redeclare,
copy, or wrap a competing full relation as a second authority. It also must
not copy STCADR08.Trace into production.

## 11. P11S-T02 — AtomicProfile and derived Rb

Define the accepted macro/view boundary:

* AtomicProfile or separate orchestration/lifecycle macro records;
* finite expansion lists with exact labels and endpoint witnesses;
* atomicity/confinement premises;
* no interleaved orchestration;
* no unaccounted yield, raise, pending async landing, or unfinished path;
* stable embedded endpoints and projection witnesses;
* an explicitly tagged optional stuttering identity.

Define Rb_orch and Rb_life from accepted AtomicProfile witnesses and R+ traces.
Rb must be a definition/derived proposition. Do not store independently
maintained base-rule constructors whose truth could diverge from R+.

A failing, unfinished, or interleaved full path must never be identified with
a successful base step.

## 12. P11S-T03 — forward simulation and trace composition

Provide:

* project/embed round-trip on the base image;
* stable(embed b);
* forward orchestration simulation;
* forward lifecycle simulation;
* concatenation of base macros to the concatenated R+ trace;
* preservation of endpoint embedding and exact expansion labels.

The single-step forward facts may follow directly from the definition of Rb,
but the multi-step trace-composition theorem must use the Control Trace append
API and retain labels/endpoints. Do not count a field projection alone as the
entire Staging K result.

## 13. P11S-T04 — profile-relative adequacy and quiescence boundary

Define AtomicAdequacy or an equivalent explicit contract. The converse may
classify only paths satisfying the chosen AtomicProfile and embedded-endpoint
premises. Its conclusion is:

* a corresponding base label/macro witness; or
* a separately permitted stuttering identity.

It must not classify arbitrary R+ traces containing failure, interleaving,
pending asynchronous work, or non-atomic yield.

Expose the hypotheses needed for a stable-image quiescence bridge:

* stable-image closure;
* completeness of the selected macro partition;
* no pending in-flight/failure branch at the endpoint;
* matching guard and provider/WF assumptions.

A fully general quietFull iff quietBase theorem is deferred unless all of
those hypotheses are concretely supplied and proved.

## 14. P11S-T05 — finite Staging evidence and gate

Create STC/Examples/Staging.lean. Reuse or adapt the finite P10 Control model
and demonstrate:

* a one-step orchestration macro;
* a multi-step lifecycle macro such as begin/finish;
* another multi-step lifecycle path such as leave/unload;
* project/embed round trip;
* forward simulation;
* one accepted atomic adequacy case;
* rejection of a wrong endpoint;
* rejection of a non-atomic label sequence;
* rejection of an interleaved/failing/unfinished path.

The example must not introduce an independent base calculus merely to make
adequacy easy.

Run:

~~~bash
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Staging.lean
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true STC/Examples/Staging.lean
lake build
python scripts/validate_definition_ledger.py docs/status/Definition-Ledger.json
python scripts/scan_lean.py STC
git diff --check
~~~

Record the raw scanner result and create
docs/status/P11-staging-handoff-report.md.

## 15. Ledger and evidence disposition

This lane does not edit Definition-Ledger.json. Its handoffs must propose
item-by-item updates without overstating completion.

Expected Control-facing review set:

~~~text
D44 D46 D47 D49 D53
L54 L55 L56 L57
T59 D60 T61 C62 T63 T64 T66
R.withdraw R.iter A.async R.fail R.full Table1
~~~

Expected Staging-facing review set:

~~~text
D44 D46 D49
R.base R.full
~~~

Rules for the proposed patch:

* architecture blockers may be recorded as closed by P9;
* a row becomes in_progress/completed only for declarations and theorems
  actually integrated in production;
* interface records earn I, substantive propositions need K, finite fixtures
  earn E;
* R.iter/R.fail may gain labelled Control integration evidence without
  erasing their earlier P3/P4 evidence;
* T59/T61/C62/T63/T64/T66 and trace-level D60 remain pending unless their
  exact full statements and hypotheses are proved;
* L68/L70/L72/T73 are outside this lane.

## 16. Handoff, merge, and reopen rules

The final lane handoff must include:

* exact base/head commits and changed files;
* public API inventory;
* P10 freeze record and proof that Staging did not modify it;
* A/I/K/E classification per declaration/theorem;
* finite positive and negative evidence;
* all focused and cumulative command outputs;
* proposed ledger/status deltas;
* deferred support, scoped, global theorem, and runtime obligations.

Do not update STC.lean or STC/Bootstrap.lean in this branch. The integration
owner adds imports after merging all parallel lanes and reruns the cumulative
gate.

Stop and request a new decision if implementation would require:

* merging orchestration and lifecycle into one untyped relation;
* adding a scheduler to the abstract state;
* dropping InFlight landing linkage or complete failure data;
* changing P3/P4 result or iterator semantics;
* making Rb authoritative or independently maintained;
* treating arbitrary full traces as one base step;
* modifying an accepted ADR artifact;
* importing a historical spike;
* weakening an observer or premise to manufacture a theorem.

Such a change requires a superseding ADR or an explicit integration ruling,
not a local convenience edit.
